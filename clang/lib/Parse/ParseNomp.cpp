//===--- ParseNomp.cpp - Nomp directives parsing ----------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
/// \file
/// This file implements parsing of all Nomp directives and clauses.
///
//===----------------------------------------------------------------------===//

#include "clang/AST/Decl.h"
#include "clang/AST/Expr.h"
#include "clang/AST/Stmt.h"
#include "clang/AST/StmtVisitor.h"
#include "clang/Lex/Preprocessor.h"
#include "clang/Lex/Token.h"
#include "clang/Parse/ParseDiagnostic.h"
#include "clang/Parse/Parser.h"
#include "clang/Sema/Ownership.h"
#include "clang/Sema/Sema.h"
#include "llvm/ADT/StringSwitch.h"

#include <iostream>

using namespace clang;

enum LibNompFunc {
  NompInvalid = -1,
  NompInit = 0,
  NompUpdate = 1,
  NompJit = 2,
  NompRun = 3,
  NompFinalize = 4,
  NompErr = 5
};
static FunctionDecl *LibNompFuncs[32] = {nullptr};

enum Directive {
  DirectiveInvalid = -1,
  DirectiveInit = 0,
  DirectiveUpdate = 1,
  DirectiveFor = 2,
  DirectiveFinalize = 3
};

enum UpdateDirection {
  UpdateInvalid = -1,
  UpdateAlloc = 0,
  UpdateTo = 1,
  UpdateFrom = 2,
  UpdateFree = 3
};

enum ArgType { TypeInteger = 1, TypeFloat = 2, TypePointer = 4 };

//==============================================================================
// Helper functions: String to Nomp types conversion
//
static inline LibNompFunc GetLibNompFunc(const llvm::StringRef name) {
  return llvm::StringSwitch<LibNompFunc>(name)
      .Case("nomp_init", NompInit)
      .Case("nomp_update", NompUpdate)
      .Case("nomp_jit", NompJit)
      .Case("nomp_run", NompRun)
      .Case("nomp_finalize", NompFinalize)
      .Default(NompInvalid);
}

static inline Directive GetDirective(const llvm::StringRef name) {
  return llvm::StringSwitch<Directive>(name)
      .Case("init", DirectiveInit)
      .Case("update", DirectiveUpdate)
      .Case("for", DirectiveFor)
      .Case("finalize", DirectiveFinalize)
      .Default(DirectiveInvalid);
}

static inline UpdateDirection GetUpdateDirection(const llvm::StringRef dirn) {
  return llvm::StringSwitch<UpdateDirection>(dirn)
      .Case("to", UpdateTo)
      .Case("from", UpdateFrom)
      .Case("alloc", UpdateAlloc)
      .Case("free", UpdateFree)
      .Default(UpdateInvalid);
}

static inline void NompHandleError(unsigned DiagID, Token &Tok, Parser &P,
                                   int LO = 0) {
  Preprocessor &PP = P.getPreprocessor();
  SourceManager &SM = PP.getSourceManager();
  FullSourceLoc loc(Tok.getLocation(), SM);
  if (LO)
    PP.Diag(Tok, DiagID) << loc.getLineNumber();
  else
    PP.Diag(Tok, DiagID) << loc.getLineNumber() << loc.getColumnNumber();
  P.SkipUntil(tok::annot_pragma_nomp_end);
}

static inline void NompHandleError3(unsigned DiagID, Token &Tok,
                                    llvm::StringRef Arg, Parser &P) {
  Preprocessor &PP = P.getPreprocessor();
  SourceManager &SM = PP.getSourceManager();
  FullSourceLoc loc(Tok.getLocation(), SM);
  PP.Diag(Tok, DiagID) << Arg << loc.getLineNumber() << loc.getColumnNumber();
  P.SkipUntil(tok::annot_pragma_nomp_end);
}
//==============================================================================
// Helper functions: Tokens to Clang Stmt conversions
//
static bool GetVariableAsFuncArg(ImplicitCastExpr *&ICE, VarDecl *&VD,
                                 Token &tok, Parser &P) {
  Sema &S = P.getActions();
  ASTContext &AST = S.getASTContext();

  tok::TokenKind TK = tok.getKind();
  if (TK != tok::identifier) {
    // If the token is not an identifier, it is an error
    NompHandleError(diag::err_nomp_identifier_expected, tok, P);
  } else {
    // Check for the declation of the identifier in current scope and
    // If not found, check on the translation Unit scope. If not found
    // in thre either, it's an error.
    DeclarationName DN = DeclarationName(tok.getIdentifierInfo());
    VD = dyn_cast_or_null<VarDecl>(
        S.LookupSingleName(P.getCurScope(), DN, SourceLocation(),
                           Sema::LookupNameKind::LookupOrdinaryName));
    if (!VD)
      VD = dyn_cast_or_null<VarDecl>(
          S.LookupSingleName(S.TUScope, DN, SourceLocation(),
                             Sema::LookupNameKind::LookupOrdinaryName));

    if (VD) {
      DeclRefExpr *DRE = DeclRefExpr::Create(
          AST, NestedNameSpecifierLoc(), SourceLocation(), VD, false,
          tok.getLocation(), VD->getType(), VK_PRValue);
      ICE = ImplicitCastExpr::Create(AST, VD->getType(), CK_LValueToRValue, DRE,
                                     nullptr, VK_PRValue, FPOptionsOverride());
      P.ConsumeToken();
      return true;
    }

    // Variable declaration not found
    NompHandleError3(diag::err_nomp_no_vardecl_found, tok, DN.getAsString(), P);
  }

  return false;
}

static CallExpr *CreateCallExpr(const ASTContext &AST, const SourceLocation &SL,
                                llvm::ArrayRef<Expr *> Args, FunctionDecl *FD) {
  DeclRefExpr *DRE =
      DeclRefExpr::Create(AST, NestedNameSpecifierLoc(), SourceLocation(), FD,
                          false, SL, FD->getType(), ExprValueKind::VK_PRValue);

  ImplicitCastExpr *ICE = ImplicitCastExpr::Create(
      AST, AST.getPointerType(FD->getType()),
      CastKind::CK_FunctionToPointerDecay, DRE, nullptr,
      ExprValueKind::VK_PRValue, FPOptionsOverride());

  return CallExpr::Create(AST, ICE, Args, FD->getCallResultType(),
                          ExprValueKind::VK_PRValue, SL, FPOptionsOverride());
}

static bool FindLibNompFuncDecl(llvm::StringRef LNF, Sema &S) {
  LibNompFunc FN = GetLibNompFunc(LNF);
  if (FN == NompInvalid)
    return false;

  IdentifierInfo &I = S.getASTContext().Idents.get(LNF);
  DeclarationName DN = DeclarationName(&I);
  LibNompFuncs[FN] = dyn_cast_or_null<FunctionDecl>(
      S.LookupSingleName(S.TUScope, DN, SourceLocation(),
                         Sema::LookupNameKind::LookupOrdinaryName));
  return LibNompFuncs[FN] != nullptr;
}

//==============================================================================
// Parse and generate calls for Nomp API functions
//
int Parser::ParseNompExpr(llvm::SmallVector<Expr *, 16> &EL) {
  ExprResult LHS = ParseAssignmentExpression();
  ExprResult ER = ParseRHSOfBinaryExpression(LHS, prec::Assignment);
  if (ER.isUsable())
    EL.push_back(ER.getAs<Expr>());
  return !ER.isUsable();
}

void Parser::ParseNompExprListUntilRParen(llvm::SmallVector<Expr *, 16> &EL,
                                          llvm::StringRef Pragma) {
  while (Tok.isNot(tok::r_paren) and Tok.isNot(tok::annot_pragma_nomp_end)) {
    ParseNompExpr(EL);
    if (Tok.isNot(tok::r_paren))
      if (!TryConsumeToken(tok::comma))
        NompHandleError3(diag::err_nomp_comma_expected, Tok, Pragma, *this);
  }

  if (!TryConsumeToken(tok::r_paren))
    NompHandleError3(diag::err_nomp_rparen_expected, Tok, Pragma, *this);
}

StmtResult Parser::ParseNompInit(const SourceLocation &SL) {
  Sema &S = getActions();
  ASTContext &AST = S.getASTContext();

  // "("
  if (!TryConsumeToken(tok::l_paren)) {
    NompHandleError3(diag::err_nomp_lparen_expected, Tok, "init", *this);
    return StmtEmpty();
  }

  llvm::SmallVector<Expr *, 16> CallArgs;
  ParseNompExprListUntilRParen(CallArgs, "init");
  if (CallArgs.size() != 3) {
    NompHandleError3(diag::err_nomp_invalid_number_of_args, Tok, "init", *this);
    return StmtEmpty();
  }

  ConsumeAnnotationToken(); // tok::annot_pragma_nomp_end
  return CreateCallExpr(AST, SL, ArrayRef<Expr *>(CallArgs),
                        LibNompFuncs[NompInit]);
}

StmtResult Parser::ParseNompUpdate(const SourceLocation &SL) {
  ASTContext &AST = getActions().getASTContext();

  // "("
  if (!TryConsumeToken(tok::l_paren)) {
    NompHandleError3(diag::err_nomp_lparen_expected, Tok, "update", *this);
    return StmtEmpty();
  }

  // Direction should be one of the following: "to", "from", "alloc", "free".
  // So, if the token is not an identifier, it is an error.
  if (Tok.isNot(tok::identifier))
    NompHandleError(diag::err_nomp_identifier_expected, Tok, *this);
  UpdateDirection dirn = GetUpdateDirection(Tok.getIdentifierInfo()->getName());
  if (dirn == UpdateInvalid) {
    NompHandleError(diag::err_nomp_invalid_update_direction, Tok, *this);
    return StmtEmpty();
  }
  ConsumeToken();

  // ":"
  if (!TryConsumeToken(tok::colon)) {
    NompHandleError3(diag::err_nomp_colon_expected, Tok, "update", *this);
    return StmtEmpty();
  }

  llvm::SmallVector<Stmt *, 16> FuncCalls;
  llvm::SmallVector<Expr *, 16> FuncArgs;
  while (Tok.isNot(tok::r_paren) and Tok.isNot(tok::annot_pragma_nomp_end)) {
    FuncArgs.clear();
    SourceLocation TL = Tok.getLocation();

    // Array pointer
    ImplicitCastExpr *ICE;
    VarDecl *VD;
    if (!GetVariableAsFuncArg(ICE, VD, Tok, *this))
      return StmtEmpty();

    const Type *T = ICE->getType().getTypePtr();
    if (!T->isPointerType()) {
      NompHandleError3(diag::err_nomp_pointer_type_expected, Tok, "update",
                       *this);
      return StmtEmpty();
    }
    FuncArgs.push_back(ICE);

    // Start offset
    if (!TryConsumeToken(tok::l_square)) {
      NompHandleError3(diag::err_nomp_lsquare_expected, Tok, "update", *this);
      return StmtEmpty();
    }
    ParseNompExpr(FuncArgs);

    // End offset
    if (!TryConsumeToken(tok::comma)) {
      NompHandleError3(diag::err_nomp_comma_expected, Tok, "update", *this);
      return StmtEmpty();
    }
    ParseNompExpr(FuncArgs);

    if (!TryConsumeToken(tok::r_square)) {
      NompHandleError3(diag::err_nomp_rsquare_expected, Tok, "update", *this);
      return StmtEmpty();
    }

    // Unit size: sizeof()
    QualType CT = T->getPointeeOrArrayElementType()->getCanonicalTypeInternal();
    UnaryExprOrTypeTraitExpr *UETT = new (AST) UnaryExprOrTypeTraitExpr(
        UETT_SizeOf, AST.getTrivialTypeSourceInfo(CT), AST.getSizeType(),
        SourceLocation(), SourceLocation());
    FuncArgs.push_back(UETT);

    // Update direction
    QualType IntTy = AST.getIntTypeForBitwidth(32, 0);
    FuncArgs.push_back(IntegerLiteral::Create(AST, llvm::APInt(32, dirn), IntTy,
                                              SourceLocation()));

    FuncCalls.push_back(
        CreateCallExpr(AST, TL, FuncArgs, LibNompFuncs[NompUpdate]));

    TryConsumeToken(tok::comma);
  }

  if (!TryConsumeToken(tok::r_paren)) {
    NompHandleError3(diag::err_nomp_rparen_expected, Tok, "update", *this);
    return StmtEmpty();
  }

  SourceLocation EL = Tok.getLocation();
  ConsumeAnnotationToken(); // tok::annot_pragma_nomp_end
  return CompoundStmt::Create(AST, ArrayRef<Stmt *>(FuncCalls),
                              FPOptionsOverride(), SL, EL);
}

namespace {
class ExternalVarRefFinder final : public StmtVisitor<ExternalVarRefFinder> {
  std::set<VarDecl *> VD_, DRE_;

public:
  ExternalVarRefFinder() {}

  void VisitCompoundStmt(CompoundStmt *S) {
    for (auto *B : S->body())
      Visit(B);
  }

  void VisitForStmt(ForStmt *S) {
    if (S->getInit())
      Visit(S->getInit());
    if (S->getCond())
      Visit(S->getCond());
    if (S->getInc())
      Visit(S->getInc());
    Visit(S->getBody());
  }

  void VisitDeclStmt(DeclStmt *S) {
    for (auto D : S->decls())
      VisitDecl(D);
  }

  void VisitDecl(Decl *D) {
    if (auto *VD = dyn_cast<VarDecl>(D)) {
      VD_.insert(VD->getCanonicalDecl());
      if (VD->hasInit())
        Visit(VD->getInit());
    }
  }

  void VisitBinaryOperator(BinaryOperator *O) {
    Visit(O->getLHS());
    Visit(O->getRHS());
  }

  void VisitArraySubscriptExpr(ArraySubscriptExpr *E) {
    Visit(E->getLHS());
    Visit(E->getRHS());
  }

  void VisitImplicitCastExpr(ImplicitCastExpr *E) { Visit(E->getSubExpr()); }

  void VisitDeclRefExpr(DeclRefExpr *DRE) {
    if (auto *VD = dyn_cast<VarDecl>(DRE->getDecl()))
      DRE_.insert(VD->getCanonicalDecl());
  }

  void GetExternalVarDecls(std::set<VarDecl *> &VDS) {
    std::set_difference(DRE_.begin(), DRE_.end(), VD_.begin(), VD_.end(),
                        std::inserter(VDS, VDS.begin()));
  }
};
} // namespace

static void ProcessForStmt(std::set<VarDecl *> &EV, std::string &KNL,
                           std::string &KArgs, const std::string &KName,
                           ForStmt *FS, const SourceManager &SM,
                           const clang::LangOptions &Opts) {
  // Find the External VarDecls in the for loop
  ExternalVarRefFinder EVRF;
  EVRF.VisitForStmt(FS);
  EVRF.GetExternalVarDecls(EV);

  clang::PrintingPolicy Policy(Opts);
  llvm::raw_string_ostream KS(KNL), KAS(KArgs);
  KS << "void " << KName << "(";
  unsigned int size = EV.size(), count = 0;
  for (auto V : EV) {
    count++, V->print(KS, Policy, 0), KAS << V->getNameAsString();
    if (count < size)
      KS << ", ", KAS << ",";
    else
      KS << ")";
  }
  KS << " {\n";

  SourceLocation BL = FS->getBeginLoc(), EL = FS->getEndLoc();
  unsigned s = SM.getFileOffset(BL), e = SM.getFileOffset(EL);
  llvm::StringRef bfr = SM.getBufferData(SM.getFileID(BL));
  unsigned n = e;
  for (; n < bfr.size() && bfr[n] != ';' && bfr[n] != '}'; n++)
    ;
  const char *ptr = bfr.data();
  KNL = KNL + std::string(ptr + s, n - s + 2);

  KS << "}";
}

static void CreateNompJitCall(llvm::SmallVector<Stmt *, 16> &Stmts,
                              ASTContext &AST, VarDecl *ID, VarDecl *ND,
                              VarDecl *GZ, VarDecl *LZ, const std::string &KNL,
                              const std::string &KArgs,
                              const std::set<VarDecl *> &EV) {
  llvm::SmallVector<Expr *, 16> FuncArgs;

  // First argument to nomp_jit() is '&id' -- output argument which assigns an
  // unique id to each kernel.
  DeclRefExpr *DRE =
      DeclRefExpr::Create(AST, NestedNameSpecifierLoc(), SourceLocation(), ID,
                          false, SourceLocation(), ID->getType(), VK_LValue);
  FuncArgs.push_back(UnaryOperator::Create(
      AST, DRE, UO_AddrOf, AST.getPointerType(DRE->getType()), VK_PRValue,
      OK_Ordinary, SourceLocation(), false, FPOptionsOverride()));

  // Second argument to nomp_jit() is '&ndim' -- output argument which sets
  // the dimension of the kernel launch.
  DRE = DeclRefExpr::Create(AST, NestedNameSpecifierLoc(), SourceLocation(), ND,
                            false, SourceLocation(), ND->getType(), VK_LValue);
  FuncArgs.push_back(UnaryOperator::Create(
      AST, DRE, UO_AddrOf, AST.getPointerType(DRE->getType()), VK_PRValue,
      OK_Ordinary, SourceLocation(), false, FPOptionsOverride()));

  // Third and fourth arguments are the launch parameters of the kernel: global
  // and local size.
  DRE = DeclRefExpr::Create(AST, NestedNameSpecifierLoc(), SourceLocation(), GZ,
                            false, SourceLocation(), GZ->getType(), VK_PRValue);
  QualType ArrayTy = LZ->getType();
  FuncArgs.push_back(
      ImplicitCastExpr::Create(AST, ArrayTy, CastKind::CK_ArrayToPointerDecay,
                               DRE, nullptr, VK_PRValue, FPOptionsOverride()));

  DRE = DeclRefExpr::Create(AST, NestedNameSpecifierLoc(), SourceLocation(), LZ,
                            false, SourceLocation(), LZ->getType(), VK_PRValue);
  FuncArgs.push_back(
      ImplicitCastExpr::Create(AST, ArrayTy, CastKind::CK_ArrayToPointerDecay,
                               DRE, nullptr, VK_PRValue, FPOptionsOverride()));

  // Fourth argument to nomp_jit() is the kernel string (or the for loop)
  QualType StrTy =
      AST.getConstantArrayType(AST.CharTy, llvm::APInt(32, KNL.size() + 1),
                               nullptr, ArrayType::Normal, 0);
  StringLiteral *KSL = StringLiteral::Create(AST, KNL, StringLiteral::Ordinary,
                                             false, StrTy, SourceLocation());
  FuncArgs.push_back(
      ImplicitCastExpr::Create(AST, StrTy, CastKind::CK_ArrayToPointerDecay,
                               KSL, nullptr, VK_PRValue, FPOptionsOverride()));

  // Fifth argument to nomp_jit() is the number of external arguments.
  QualType IntTy = AST.getIntTypeForBitwidth(32, 0);
  FuncArgs.push_back(IntegerLiteral::Create(AST, llvm::APInt(32, EV.size()),
                                            IntTy, SourceLocation()));

  // Sixth argument to nomp_jit() is the kernel arg names in a comma separated
  // string. We need this to evaluate the loop bounds
  StringLiteral *KASL = StringLiteral::Create(
      AST, KArgs, StringLiteral::Ordinary, false, StrTy, SourceLocation());
  FuncArgs.push_back(
      ImplicitCastExpr::Create(AST, StrTy, CastKind::CK_ArrayToPointerDecay,
                               KASL, nullptr, VK_PRValue, FPOptionsOverride()));

  for (auto V : EV) {
    // We will either have {NOMP_SCALAR, sizeof(Type), DRE(Addr_Of())} or
    // {NOMP_PTR, sizeof(Pointee Type), DRE()} based on if T is a pointer type
    // or not.
    QualType VT = V->getType();
    const Type *T = VT.getTypePtrOrNull();
    if (T) {
      FuncArgs.push_back(IntegerLiteral::Create(
          AST,
          llvm::APInt(32, TypeInteger * T->isIntegerType() +
                              TypeFloat * T->isFloatingType() +
                              TypePointer * T->isPointerType()),
          IntTy, SourceLocation()));

      QualType TT = T->isPointerType() ? T->getPointeeType() : VT;
      FuncArgs.push_back(new (AST) UnaryExprOrTypeTraitExpr(
          UETT_SizeOf, AST.getTrivialTypeSourceInfo(TT), AST.getSizeType(),
          SourceLocation(), SourceLocation()));

      DeclRefExpr *DRE =
          DeclRefExpr::Create(AST, NestedNameSpecifierLoc(), SourceLocation(),
                              V, false, SourceLocation(), VT, VK_PRValue);
      if (T->isPointerType())
        FuncArgs.push_back(DRE);
      else
        FuncArgs.push_back(UnaryOperator::Create(
            AST, DRE, UO_AddrOf, AST.getPointerType(VT), VK_PRValue,
            OK_Ordinary, SourceLocation(), false, FPOptionsOverride()));
    }
  }

  Stmts.push_back(CreateCallExpr(AST, SourceLocation(),
                                 ArrayRef<Expr *>(FuncArgs),
                                 LibNompFuncs[NompJit]));
}

static void CreateNompRunCall(llvm::SmallVector<Stmt *, 16> &Stmts,
                              ASTContext &AST, VarDecl *ID, VarDecl *ND,
                              VarDecl *GZ, VarDecl *LZ,
                              std::set<VarDecl *> EV) {
  llvm::SmallVector<Expr *, 16> FuncArgs;

  // First argument to nomp_run() is 'id' -- output argument which assigns an
  // unique id to each kernel.
  DeclRefExpr *DRE =
      DeclRefExpr::Create(AST, NestedNameSpecifierLoc(), SourceLocation(), ID,
                          false, SourceLocation(), ID->getType(), VK_LValue);
  FuncArgs.push_back(DRE);

  DRE = DeclRefExpr::Create(AST, NestedNameSpecifierLoc(), SourceLocation(), ND,
                            false, SourceLocation(), ND->getType(), VK_LValue);
  FuncArgs.push_back(DRE);

  DRE = DeclRefExpr::Create(AST, NestedNameSpecifierLoc(), SourceLocation(), GZ,
                            false, SourceLocation(), GZ->getType(), VK_PRValue);
  FuncArgs.push_back(DRE);

  DRE = DeclRefExpr::Create(AST, NestedNameSpecifierLoc(), SourceLocation(), LZ,
                            false, SourceLocation(), LZ->getType(), VK_PRValue);
  FuncArgs.push_back(DRE);

  QualType IntTy = AST.getIntTypeForBitwidth(32, 0);
  clang::IntegerLiteral *NA = IntegerLiteral::Create(
      AST, llvm::APInt(32, EV.size()), IntTy, SourceLocation());
  FuncArgs.push_back(NA);

  for (auto V : EV) {
    QualType VT = V->getType();
    const Type *T = VT.getTypePtrOrNull();
    if (T) {
      FuncArgs.push_back(IntegerLiteral::Create(
          AST,
          llvm::APInt(32, TypeInteger * T->isIntegerType() +
                              TypeFloat * T->isFloatingType() +
                              TypePointer * T->isPointerType()),
          IntTy, SourceLocation()));

      DeclRefExpr *DRE =
          DeclRefExpr::Create(AST, NestedNameSpecifierLoc(), SourceLocation(),
                              V, false, SourceLocation(), VT, VK_PRValue);
      if (T->isPointerType())
        FuncArgs.push_back(DRE);
      else {
        FuncArgs.push_back(UnaryOperator::Create(
            AST, DRE, UO_AddrOf, AST.getPointerType(VT), VK_PRValue,
            OK_Ordinary, SourceLocation(), false, FPOptionsOverride()));
        FuncArgs.push_back(new (AST) UnaryExprOrTypeTraitExpr(
            UETT_SizeOf, AST.getTrivialTypeSourceInfo(VT), AST.getSizeType(),
            SourceLocation(), SourceLocation()));
      }
    }
  }

  Stmts.push_back(CreateCallExpr(AST, SourceLocation(),
                                 ArrayRef<Expr *>(FuncArgs),
                                 LibNompFuncs[NompRun]));
}

StmtResult Parser::ParseNompFor(const SourceLocation &SL) {
  Sema &S = getActions();
  ASTContext &AST = S.getASTContext();

  if (!TryConsumeToken(tok::annot_pragma_nomp_end)) {
    NompHandleError3(diag::err_nomp_eod_expected, Tok, "for", *this);
    return StmtEmpty();
  }

  // Check if the next token is tok::kw_for. If not, exit. We should skip
  // comments if they exist -- but not doing it right now. TODO for future.
  if (Tok.isNot(tok::kw_for)) {
    NompHandleError3(diag::err_nomp_for_expected, Tok, "for", *this);
    return StmtEmpty();
  }

  // Parse the for statement
  std::set<VarDecl *> EV;
  std::string KNL, KArgs;
  // Kenel name is set to `loopy_kernel` for now -- user should be able to set
  // this.
  std::string KName = "loopy_kernel";
  ForStmt *FS = ParseForStatement(nullptr).getAs<ForStmt>();
  ProcessForStmt(EV, KNL, KArgs, KName, FS,
                 getPreprocessor().getSourceManager(), AST.getLangOpts());

  // We are going to create all our statements (declarations, function calls)
  // into the following vector and then create a compound statement out of it.
  llvm::SmallVector<Stmt *, 16> Stmts;

  // We will collect the DeclStmt in the following array.
  llvm::SmallVector<Decl *, 3> D;

  // First, let's create the statement `static int id = -1, ndim = -1;` both of
  // which are passed as output arguments to nomp_jit()
  QualType IntTy = AST.getIntTypeForBitwidth(32, 1);
  VarDecl *ID =
      VarDecl::Create(AST, S.CurContext, SL, SL, &AST.Idents.get("id"), IntTy,
                      AST.getTrivialTypeSourceInfo(IntTy), SC_Static);
  UnaryOperator *M1 = UnaryOperator::Create(
      AST, IntegerLiteral::Create(AST, llvm::APInt(32, 1), IntTy, SL), UO_Minus,
      IntTy, VK_LValue, OK_Ordinary, SL, false, FPOptionsOverride());
  ID->setInit(M1);
  D.push_back(ID);

  VarDecl *ND =
      VarDecl::Create(AST, S.CurContext, SL, SL, &AST.Idents.get("ndim"), IntTy,
                      AST.getTrivialTypeSourceInfo(IntTy), SC_Static);
  ND->setInit(M1);
  D.push_back(ND);

  Stmts.push_back(
      new (AST) DeclStmt(DeclGroupRef::Create(AST, D.begin(), 2), SL, SL));

  // Now let's create the decl for `size_t gz[3], lz[3];` which are also passed
  // as output argument to nomp_jit().
  QualType ArrayTy = AST.getConstantArrayType(
      AST.getSizeType(), llvm::APInt(32, 3), nullptr, ArrayType::Normal, 0);
  VarDecl *GZ =
      VarDecl::Create(AST, S.CurContext, SL, SL, &AST.Idents.get("gz"), ArrayTy,
                      AST.getTrivialTypeSourceInfo(ArrayTy), SC_Static);
  D.clear();
  D.push_back(GZ);
  VarDecl *LZ =
      VarDecl::Create(AST, S.CurContext, SL, SL, &AST.Idents.get("lz"), ArrayTy,
                      AST.getTrivialTypeSourceInfo(ArrayTy), SC_Static);
  D.push_back(LZ);
  Stmts.push_back(
      new (AST) DeclStmt(DeclGroupRef::Create(AST, D.begin(), 2), SL, SL));

  // Next we create the AST node for the function call nomp_jit(). To do that
  // we create the func args to nomp_jit().
  CreateNompJitCall(Stmts, AST, ID, ND, GZ, LZ, KNL, KArgs, EV);

  // Next we create AST node for nomp_run().
  CreateNompRunCall(Stmts, AST, ID, ND, GZ, LZ, EV);

  return CompoundStmt::Create(AST, ArrayRef<Stmt *>(Stmts), FPOptionsOverride(),
                              SL, SL);
}

StmtResult Parser::ParseNompFinalize(const SourceLocation &SL) {
  ASTContext &AST = getActions().getASTContext();

  if (!TryConsumeToken(tok::annot_pragma_nomp_end)) {
    NompHandleError3(diag::err_nomp_eod_expected, Tok, "finalize", *this);
    return StmtEmpty();
  }

  return CreateCallExpr(AST, SL, ArrayRef<Expr *>(),
                        LibNompFuncs[NompFinalize]);
}

//==============================================================================
// Parsing of NOMP directives.
//
//       init-directive:
//         annot_pragma_nomp 'init' simple-variable-list
//         annot_pragma_nomp_end
//       finalize-directive:
//         annot_pragma_nomp 'finalize'
//         annot_pragma_nomp_end
//       update-directive:
//         annot_pragma_nomp ['update' direction simple-variable-list]+
//         annot_pragma_nomp_end
//
StmtResult Parser::ParseNompDirective(ParsedStmtContext StmtCtx) {
  // Fill the libnomp function declaration array: LibNompFuncs
  Sema &S = getActions();
  FindLibNompFuncDecl("nomp_init", S);
  FindLibNompFuncDecl("nomp_update", S);
  FindLibNompFuncDecl("nomp_jit", S);
  FindLibNompFuncDecl("nomp_run", S);
  FindLibNompFuncDecl("nomp_finalize", S);

  SourceLocation SL = Tok.getLocation();
  // tok::annot_pragma_nomp
  ConsumeAnnotationToken();

  StmtResult result = StmtEmpty();
  llvm::StringRef DN("");
  if (Tok.is(tok::identifier))
    DN = Tok.getIdentifierInfo()->getName();
  else if (Tok.is(tok::kw_for))
    DN = llvm::StringRef("for");
  else
    return result;
  ConsumeToken();

  Directive D = GetDirective(DN);
  switch (D) {
  case DirectiveInit:
    result = ParseNompInit(SL);
    break;
  case DirectiveUpdate:
    result = ParseNompUpdate(SL);
    break;
  case DirectiveFor:
    result = ParseNompFor(SL);
    break;
  case DirectiveFinalize:
    result = ParseNompFinalize(SL);
    break;
  case DirectiveInvalid:
    NompHandleError(diag::err_nomp_invalid_directive, Tok, *this, 1);
    break;
  }

  return result;
}
