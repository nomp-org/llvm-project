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
  NompSync = 5,
  NompErr = 6
};
static FunctionDecl *LibNompFuncs[32] = {nullptr};

enum Directive {
  DirectiveInvalid = -1,
  DirectiveInit = 0,
  DirectiveUpdate = 1,
  DirectiveFor = 2,
  DirectiveSync = 3,
  DirectiveFinalize = 4
};

enum ForClause {
  ForClauseInvalid = -1,
  ForClauseJit = 0,
  ForClauseTransform = 1,
  ForClauseAnnotate = 2,
  ForClauseReduce = 3,
  ForClauseName = 4
};
std::string ForClauses[16] = {"jit", "transform", "annotate", "reduce", "name"};

// FIXME: Following enum UpdateDirection should be based on `nomp.h` and
// shouldn't be hard-coded here.
enum UpdateDirection {
  UpdateInvalid = -1,
  UpdateAlloc = 1,
  UpdateTo = 2,
  UpdateFrom = 4,
  UpdateFree = 8
};

// FIXME: Following enum ArgType should be based on `nomp.h` and shouldn't be
// hard-coded here.
enum ArgType {
  TypeInt = 2048,
  TypeUInt = 4096,
  TypeFloat = 8192,
  TypePointer = 16384
};

//==============================================================================
// Helper functions to generate C types.
//
static inline QualType getIntType(const ASTContext &AST) {
  return AST.getIntTypeForBitwidth(32, 1);
}

static inline QualType getConstantArrayType(const ASTContext &AST,
                                            const QualType QT, size_t size,
                                            ArrayType::ArraySizeModifier AT) {
  return AST.getConstantArrayType(QT, llvm::APInt(32, size), nullptr, AT, 0);
}

//==============================================================================
// Helper functions for string to nomp type conversion
//
static inline LibNompFunc GetLibNompFunc(const llvm::StringRef Name) {
  return llvm::StringSwitch<LibNompFunc>(Name)
      .Case("nomp_init", NompInit)
      .Case("nomp_update", NompUpdate)
      .Case("nomp_jit", NompJit)
      .Case("nomp_run", NompRun)
      .Case("nomp_sync", NompSync)
      .Case("nomp_finalize", NompFinalize)
      .Default(NompInvalid);
}

static inline Directive GetDirective(const llvm::StringRef Name) {
  return llvm::StringSwitch<Directive>(Name)
      .Case("init", DirectiveInit)
      .Case("update", DirectiveUpdate)
      .Case("for", DirectiveFor)
      .Case("sync", DirectiveSync)
      .Case("finalize", DirectiveFinalize)
      .Default(DirectiveInvalid);
}

static inline UpdateDirection GetUpdateDirection(const Token &Tok) {
  if (Tok.isNot(tok::identifier))
    return UpdateInvalid;

  return llvm::StringSwitch<UpdateDirection>(Tok.getIdentifierInfo()->getName())
      .Case("to", UpdateTo)
      .Case("from", UpdateFrom)
      .Case("alloc", UpdateAlloc)
      .Case("free", UpdateFree)
      .Default(UpdateInvalid);
}

static inline ForClause GetForClause(const llvm::StringRef Pragma) {
  return llvm::StringSwitch<ForClause>(Pragma)
      .Case("jit", ForClauseJit)
      .Case("transform", ForClauseTransform)
      .Case("annotate", ForClauseAnnotate)
      .Case("reduce", ForClauseReduce)
      .Case("name", ForClauseName)
      .Default(ForClauseInvalid);
}

//==============================================================================
// Error handling
//
static inline void NompHandleError(unsigned DiagID, Token &Tok, Parser &P,
                                   llvm::StringRef Arg = StringRef()) {
  Preprocessor &PP = P.getPreprocessor();
  SourceManager &SM = PP.getSourceManager();
  FullSourceLoc Loc(Tok.getLocation(), SM);
  if (Arg.empty())
    PP.Diag(Tok, DiagID) << Loc.getLineNumber() << Loc.getColumnNumber();
  else
    PP.Diag(Tok, DiagID) << Arg << Loc.getLineNumber() << Loc.getColumnNumber();
  P.SkipUntil(tok::annot_pragma_nomp_end);
}

static inline void NompHandleError(unsigned DiagID, SourceLocation SL,
                                   ASTContext &AST,
                                   llvm::StringRef Arg = StringRef()) {
  SourceManager &SM = AST.getSourceManager();
  FullSourceLoc Loc(SL, SM);
  if (Arg.empty())
    AST.getDiagnostics().Report(Loc, DiagID)
        << Loc.getLineNumber() << Loc.getColumnNumber();
  else
    AST.getDiagnostics().Report(Loc, DiagID)
        << Loc.getLineNumber() << Loc.getColumnNumber() << Arg;
}

//==============================================================================
// Helper functions: Tokens to Clang Stmt conversions
//
static VarDecl *LookupVarDecl(Token &tok, Parser &P) {
  Sema &S = P.getActions();
  tok::TokenKind TK = tok.getKind();
  if (TK != tok::identifier) {
    // If the token is not an identifier, it is an error
    NompHandleError(diag::err_nomp_identifier_expected, tok, P);
    return nullptr;
  }

  // Check for the declaration of the identifier in current scope and
  // If not found, check on the translation Unit scope. If still not found,
  // it's an error.
  DeclarationName DN = DeclarationName(tok.getIdentifierInfo());
  VarDecl *VD = dyn_cast_or_null<VarDecl>(
      S.LookupSingleName(P.getCurScope(), DN, SourceLocation(),
                         Sema::LookupNameKind::LookupOrdinaryName));
  if (!VD) {
    VD = dyn_cast_or_null<VarDecl>(
        S.LookupSingleName(S.TUScope, DN, SourceLocation(),
                           Sema::LookupNameKind::LookupOrdinaryName));
  }
  return VD;
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

static bool FindLibNompFunctionDecl(llvm::StringRef LNF, Sema &S) {
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
// Helper functions to parse expression and convert them to other expressions
//
Expr *Parser::ParseNompExpr() {
  ExprResult LHS = ParseAssignmentExpression();
  ExprResult ER = ParseRHSOfBinaryExpression(LHS, prec::Assignment);
  return ER.isUsable() ? ER.getAs<Expr>() : nullptr;
}

void Parser::ParseNompExprListUntilRParen(llvm::SmallVector<Expr *, 16> &EL,
                                          llvm::StringRef Pragma) {
  while (Tok.isNot(tok::r_paren) and Tok.isNot(tok::annot_pragma_nomp_end)) {
    if (Expr *E = ParseNompExpr())
      EL.push_back(E);
    if (Tok.isNot(tok::r_paren)) {
      if (!TryConsumeToken(tok::comma))
        NompHandleError(diag::err_nomp_comma_expected, Tok, *this, Pragma);
    }
  }

  if (!TryConsumeToken(tok::r_paren))
    NompHandleError(diag::err_nomp_rparen_expected, Tok, *this, Pragma);
}

static Expr *ExprToArgc(Expr *E, ASTContext &AST) {
  const Type *T = E->getType().getTypePtr();
  if (!T->isIntegerType() && !T->isFloatingType()) {
    NompHandleError(diag::err_nomp_function_arg_invalid, E->getExprLoc(), AST,
                    "Parameter `argc` of nomp_init() must be an Integer type.");
    return nullptr;
  }

  // If this is a DRE, we need to do LValueToRvalue cast. Otherwise, we just
  // set the Argc to E.
  QualType QT = getIntType(AST);
  Expr *Argc = E;
  if (DeclRefExpr *DRE = dyn_cast_or_null<DeclRefExpr>(E)) {
    Argc = ImplicitCastExpr::Create(
        AST, DRE->getType(), CastKind::CK_LValueToRValue, DRE, nullptr,
        ExprValueKind::VK_PRValue, FPOptionsOverride());
  }

  // If this is a floating type, we need to do FloatingToIntegral cast.
  if (T->isFloatingType()) {
    Argc = ImplicitCastExpr::Create(AST, QT, CastKind::CK_FloatingToIntegral,
                                    Argc, nullptr, ExprValueKind::VK_PRValue,
                                    FPOptionsOverride());
  }

  return Argc;
}

static Expr *ExprToArgv(Expr *E, ASTContext &AST) {
#define check_cond(cond)                                                       \
  {                                                                            \
    if (!cond) {                                                               \
      NompHandleError(diag::err_nomp_function_arg_invalid, E->getExprLoc(),    \
                      AST,                                                     \
                      "Parameter `argv` of nomp_init() must be an variable "   \
                      "which reference an array of C-strings or "              \
                      "pointer to an array of C-strings.");                    \
      return nullptr;                                                          \
    }                                                                          \
  }

  // We should have a variable pointing to array of C-strings or a pointer to
  // an array of C-strings as the argv.

  // So, we first check if this is a DeclRefExpr since we are only accepting
  // variables to pointer or array types.
  bool IsVariable = false;
  if (DeclRefExpr *DRE = dyn_cast_or_null<DeclRefExpr>(E)) {
    // If this is a DeclRefExpr, we need to check if it is a variable.
    if (isa<VarDecl>(DRE->getDecl()))
      IsVariable = true;
  }
  check_cond(IsVariable);

  // Then, check if it is a variable of an array or a pointer type.
  bool IsArrayOrPointer = false;
  const Type *T = E->getType().getTypePtr();
  if (T->isPointerType() || T->isArrayType())
    IsArrayOrPointer = true;
  check_cond(IsArrayOrPointer);

  // If it is an array or a pointer, then we check if the base type is a
  // C-string.
  bool IsCString = false;
  const Type *B = T->getPointeeOrArrayElementType();
  if (B->isPointerType() && B->getPointeeType()->isCharType())
    IsCString = true;
  check_cond(IsCString);

  // Okay, we have an array of C-strings or a pointer to an array of C-strings.
  QualType QT =
      AST.getPointerType(AST.getPointerType(AST.getConstType(AST.CharTy)));
  // If this is an array, we need to do ArrayToPointerDecay cast.
  if (T->isArrayType()) {
    return ImplicitCastExpr::Create(AST, QT, CastKind::CK_ArrayToPointerDecay,
                                    E, nullptr, ExprValueKind::VK_PRValue,
                                    FPOptionsOverride());
  }

  // If this is a pointer type, we do an LValueToRValue cast.
  if (T->isPointerType()) {
    return ImplicitCastExpr::Create(AST, QT, CastKind::CK_LValueToRValue, E,
                                    nullptr, ExprValueKind::VK_PRValue,
                                    FPOptionsOverride());
  }

  return nullptr;

#undef check_cond
}

//==============================================================================
// Parse and generate calls for Nomp API functions
//
StmtResult Parser::ParseNompInit(const SourceLocation &SL) {
  Sema &S = getActions();
  ASTContext &AST = S.getASTContext();

  // "("
  if (!TryConsumeToken(tok::l_paren)) {
    NompHandleError(diag::err_nomp_lparen_expected, Tok, *this, "init");
    return StmtEmpty();
  }

  llvm::SmallVector<Expr *, 16> InitArgs;
  // Parse everything till ")"
  ParseNompExprListUntilRParen(InitArgs, "init");

  // Check if we get the expected number of arguments.
  if (InitArgs.size() != 2) {
    NompHandleError(diag::err_nomp_invalid_number_of_args, Tok, *this, "init");
    return StmtEmpty();
  }

  // Convert Expr* to function arguments.
  llvm::SmallVector<Expr *, 2> FuncArgs;
  Expr *Argv = ExprToArgv(InitArgs.pop_back_val(), AST);
  Expr *Argc = ExprToArgc(InitArgs.pop_back_val(), AST);
  FuncArgs.push_back(Argc);
  FuncArgs.push_back(Argv);

  ConsumeAnnotationToken(); // tok::annot_pragma_nomp_end

  return CreateCallExpr(AST, SL, ArrayRef<Expr *>(FuncArgs),
                        LibNompFuncs[NompInit]);
}

StmtResult Parser::ParseNompUpdate(const SourceLocation &SL) {
  ASTContext &AST = getActions().getASTContext();

  // "("
  if (!TryConsumeToken(tok::l_paren)) {
    NompHandleError(diag::err_nomp_lparen_expected, Tok, *this, "update");
    return StmtEmpty();
  }

  // Direction should be one of the following: "to", "from", "alloc", "free".
  // So, if the token is not an identifier, it is an error.
  UpdateDirection dirn = GetUpdateDirection(Tok);
  if (dirn == UpdateInvalid) {
    NompHandleError(diag::err_nomp_invalid_update_direction, Tok, *this);
    return StmtEmpty();
  }
  ConsumeToken();

  // ":"
  if (!TryConsumeToken(tok::colon)) {
    NompHandleError(diag::err_nomp_colon_expected, Tok, *this, "update");
    return StmtEmpty();
  }

  llvm::SmallVector<Stmt *, 16> FuncCalls;
  llvm::SmallVector<Expr *, 16> FuncArgs;
  while (Tok.isNot(tok::r_paren) and Tok.isNot(tok::annot_pragma_nomp_end)) {
    FuncArgs.clear();
    SourceLocation TL = Tok.getLocation();

    // Array pointer
    VarDecl *VD = LookupVarDecl(Tok, *this);
    if (!VD) {
      // Variable declaration not found
      DeclarationName DN = DeclarationName(Tok.getIdentifierInfo());
      NompHandleError(diag::err_nomp_no_vardecl_found, Tok, *this,
                      DN.getAsString());
      return StmtEmpty();
    }

    const Type *T = VD->getType().getTypePtr();
    if (!T->isPointerType() && !T->isArrayType()) {
      NompHandleError(diag::err_nomp_pointer_type_expected, Tok, *this,
                      "update");
      return StmtEmpty();
    }

    DeclRefExpr *DRE =
        DeclRefExpr::Create(AST, NestedNameSpecifierLoc(), SourceLocation(), VD,
                            false, TL, VD->getType(), VK_PRValue);
    QualType VoidPtrTy = AST.getPointerType(AST.getConstType(AST.VoidTy));
    auto CK = CastKind::CK_LValueToRValue;
    if (T->isArrayType())
      CK = CK_ArrayToPointerDecay;
    ImplicitCastExpr *ICE = ImplicitCastExpr::Create(
        AST, VoidPtrTy, CK, DRE, nullptr, VK_PRValue, FPOptionsOverride());
    FuncArgs.push_back(ICE);
    ConsumeToken();

    // Start offset
    if (!TryConsumeToken(tok::l_square)) {
      NompHandleError(diag::err_nomp_lsquare_expected, Tok, *this, "update");
      return StmtEmpty();
    }
    Expr *E = ParseNompExpr();
    if (!E) {
      NompHandleError(diag::err_nomp_invalid_expression, Tok, *this);
      return StmtEmpty();
    }
    ICE = ImplicitCastExpr::Create(AST, AST.getSizeType(),
                                   CastKind::CK_LValueToRValue, E, nullptr,
                                   VK_PRValue, FPOptionsOverride());
    FuncArgs.push_back(ICE);

    // End offset
    if (!TryConsumeToken(tok::comma)) {
      NompHandleError(diag::err_nomp_comma_expected, Tok, *this, "update");
      return StmtEmpty();
    }
    E = ParseNompExpr();
    if (!E) {
      NompHandleError(diag::err_nomp_invalid_expression, Tok, *this);
      return StmtEmpty();
    }
    ICE = ImplicitCastExpr::Create(AST, AST.getSizeType(),
                                   CastKind::CK_LValueToRValue, E, nullptr,
                                   VK_PRValue, FPOptionsOverride());
    FuncArgs.push_back(ICE);

    if (!TryConsumeToken(tok::r_square)) {
      NompHandleError(diag::err_nomp_rsquare_expected, Tok, *this, "update");
      return StmtEmpty();
    }

    // Unit size: sizeof()
    QualType CT = T->getPointeeOrArrayElementType()->getCanonicalTypeInternal();
    UnaryExprOrTypeTraitExpr *UETT = new (AST) UnaryExprOrTypeTraitExpr(
        UETT_SizeOf, AST.getTrivialTypeSourceInfo(CT), AST.getSizeType(),
        SourceLocation(), SourceLocation());
    FuncArgs.push_back(UETT);

    // Update direction
    FuncArgs.push_back(IntegerLiteral::Create(
        AST, llvm::APInt(32, dirn), getIntType(AST), SourceLocation()));

    FuncCalls.push_back(
        CreateCallExpr(AST, TL, FuncArgs, LibNompFuncs[NompUpdate]));

    TryConsumeToken(tok::comma);
  }

  if (!TryConsumeToken(tok::r_paren)) {
    NompHandleError(diag::err_nomp_rparen_expected, Tok, *this, "update");
    return StmtEmpty();
  }

  SourceLocation EL = Tok.getLocation();
  ConsumeAnnotationToken(); // tok::annot_pragma_nomp_end
  return CompoundStmt::Create(AST, ArrayRef<Stmt *>(FuncCalls),
                              FPOptionsOverride(), SL, EL);
}

namespace {
class PreprocessVisitor final : public StmtVisitor<PreprocessVisitor, void> {
  std::set<VarDecl *> VD_, DRE_;
  std::set<std::string> Names_;

public:
  PreprocessVisitor(ForStmt *FS) { VisitForStmt(FS); }

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
    if (auto *VD = dyn_cast<VarDecl>(D))
      VisitVarDecl(VD);
    if (auto *FD = dyn_cast<FunctionDecl>(D))
      NompHandleError(diag::err_nomp_func_decl_in_kernel, FD->getLocation(),
                      FD->getASTContext());
  }

  void VisitVarDecl(VarDecl *VD) {
    auto name = VD->getNameAsString();
    if (Names_.find(name) != Names_.end()) {
      do {
        name = name + "_";
      } while (Names_.find(name) != Names_.end());
      IdentifierInfo &I = VD->getASTContext().Idents.get(name);
      DeclarationName DN(&I);
      VD->setDeclName(DN);
    }
    Names_.insert(name);

    VD_.insert(VD->getCanonicalDecl());
    if (VD->hasInit())
      Visit(VD->getInit());
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

  void VisitParenExpr(ParenExpr *E) { Visit(E->getSubExpr()); }

  void VisitConditionalOperator(ConditionalOperator *E) {
    Visit(E->getCond());
    Visit(E->getLHS());
    Visit(E->getRHS());
  }

  void VisitIfStmt(IfStmt *S) {
    Visit(S->getCond());
    Visit(S->getThen());
    if (S->hasElseStorage())
      Visit(S->getElse());
  }

  void VisitDeclRefExpr(DeclRefExpr *DRE) {
    if (auto *VD = dyn_cast<VarDecl>(DRE->getDecl()))
      DRE_.insert(VD->getCanonicalDecl());

    if (auto *FD = dyn_cast<FunctionDecl>(DRE->getDecl()))
      NompHandleError(diag::err_nomp_func_call_in_kernel, FD->getLocation(),
                      FD->getASTContext());
  }

  void GetExternalVarDecls(std::set<VarDecl *> &EVD) {
    std::set_difference(DRE_.begin(), DRE_.end(), VD_.begin(), VD_.end(),
                        std::inserter(EVD, EVD.begin()));
  }
}; // PreprocessVisitor

} // namespace

static void GetKernel(std::string &Kernel, const std::string &KernelName,
                      const std::set<VarDecl *> &EV, const ForStmt *FS,
                      const clang::LangOptions &Opts) {
  clang::PrintingPolicy Policy(Opts);
  Policy.SuppressInitializers = false;
  Policy.PrintCanonicalTypes = true;

  llvm::raw_string_ostream OS(Kernel);
  OS << "void " << KernelName << "(";

  unsigned size = EV.size(), count = 0;
  for (auto V : EV) {
    V->print(OS, Policy, 0);
    count++;
    if (count < size)
      OS << ",";
    else
      OS << ")";
  }
  OS << " {\n";

  FS->printPretty(OS, nullptr, Policy, 0);
  OS << "}";
}

static void
CreateNompJitCall(llvm::SmallVector<Stmt *, 16> &Stmts, ASTContext &AST,
                  VarDecl *ID, VarDecl *VKNL, VarDecl *VCLS,
                  std::set<VarDecl *> &EV,
                  const std::vector<std::string> &reductionVariables) {
  llvm::SmallVector<Expr *, 16> FuncArgs;
  SourceLocation SL = SourceLocation();

  // 1st argument is '&id' -- output argument which assigns an unique id to
  // each kernel.
  DeclRefExpr *DRE =
      DeclRefExpr::Create(AST, NestedNameSpecifierLoc(), SourceLocation(), ID,
                          false, SourceLocation(), ID->getType(), VK_LValue);
  FuncArgs.push_back(UnaryOperator::Create(
      AST, DRE, UO_AddrOf, AST.getPointerType(DRE->getType()), VK_PRValue,
      OK_Ordinary, SL, false, FPOptionsOverride()));

  // 2nd argument is the kernel string (or the for loop) wrapped inside a
  // function.
  QualType CharPtrTy1 = AST.getPointerType(AST.getConstType(AST.CharTy));
  DRE = DeclRefExpr::Create(AST, NestedNameSpecifierLoc(), SL, VKNL, false, SL,
                            VKNL->getType(), VK_LValue);
  FuncArgs.push_back(ImplicitCastExpr::Create(
      AST, CharPtrTy1, CastKind::CK_ArrayToPointerDecay, DRE, nullptr,
      VK_PRValue, FPOptionsOverride()));

  // 3rd argument is the auxiliary pragmas nomp allow after `#pragma nomp for`
  // Currently, we support `transform`, `annotate` and `reduce`.
  QualType CharPtrTy2 = AST.getPointerType(CharPtrTy1);
  DRE = DeclRefExpr::Create(AST, NestedNameSpecifierLoc(), SL, VCLS, false, SL,
                            VCLS->getType(), VK_LValue);
  FuncArgs.push_back(ImplicitCastExpr::Create(
      AST, CharPtrTy2, CastKind::CK_ArrayToPointerDecay, DRE, nullptr,
      VK_PRValue, FPOptionsOverride()));

  // 4th argument to nomp_jit() is 'nargs' -- total number of arguments to
  // the kernel
  int nargs = EV.size();
  QualType IntTy = getIntType(AST);
  FuncArgs.push_back(IntegerLiteral::Create(AST, llvm::APInt(32, nargs), IntTy,
                                            SourceLocation()));

  QualType StrTy = AST.getPointerType(AST.CharTy);
  for (auto V : EV) {
    QualType QT = V->getType();
    const Type *T = QT.getTypePtrOrNull();
    if (T) {
      // Name of the variable as a string.
      std::string name = V->getNameAsString();
      QualType NameStrTy = getConstantArrayType(
          AST, AST.CharTy, name.size() + 1, ArrayType::Normal);
      StringLiteral *SL =
          StringLiteral::Create(AST, name, StringLiteral::Ordinary, false,
                                NameStrTy, SourceLocation());
      ImplicitCastExpr *ICE =
          ImplicitCastExpr::Create(AST, StrTy, CK_ArrayToPointerDecay, SL,
                                   nullptr, VK_PRValue, FPOptionsOverride());
      FuncArgs.push_back(ICE);

      if (T->isArrayType())
        QT = AST.getBaseElementType(dyn_cast<ArrayType>(T));
      else if (T->isPointerType())
        QT = dyn_cast<PointerType>(T)->getPointeeType();
      TypeSourceInfo *TSI = AST.getTrivialTypeSourceInfo(QT);

      // sizeof(variable)
      FuncArgs.push_back(new (AST) UnaryExprOrTypeTraitExpr(
          UETT_SizeOf, TSI, AST.getSizeType(), SourceLocation(),
          SourceLocation()));

      // Check if the variable is part of a reduction since we need to pass the
      // pointee type or base element type in that case.
      Type *T1 = const_cast<Type *>(T);
      if (std::find(reductionVariables.begin(), reductionVariables.end(),
                    name) != reductionVariables.end())
        T1 = const_cast<Type *>(QT.getTypePtrOrNull());

      // Find the nomp type.
      int type = TypeInt * T1->isSignedIntegerType() +
                 TypeFloat * T1->isFloatingType() +
                 TypeUInt * T1->isUnsignedIntegerType() +
                 TypePointer * (T1->isPointerType() || T1->isArrayType());

      if (type == 0) {
        NompHandleError(diag::err_nomp_function_arg_invalid, V->getLocation(),
                        AST);
      }

      FuncArgs.push_back(IntegerLiteral::Create(AST, llvm::APInt(32, type),
                                                IntTy, SourceLocation()));
    }
  }

  Stmts.push_back(CreateCallExpr(AST, SourceLocation(),
                                 ArrayRef<Expr *>(FuncArgs),
                                 LibNompFuncs[NompJit]));
}

static void CreateNompRunCall(llvm::SmallVector<Stmt *, 16> &Stmts,
                              ASTContext &AST, VarDecl *ID,
                              std::set<VarDecl *> &EV) {
  llvm::SmallVector<Expr *, 16> FuncArgs;

  // First argument to nomp_run() is 'id' -- input argument which passes an
  // unique id for each kernel.
  DeclRefExpr *DRE =
      DeclRefExpr::Create(AST, NestedNameSpecifierLoc(), SourceLocation(), ID,
                          false, SourceLocation(), ID->getType(), VK_LValue);
  FuncArgs.push_back(
      ImplicitCastExpr::Create(AST, ID->getType(), CastKind::CK_LValueToRValue,
                               DRE, nullptr, VK_PRValue, FPOptionsOverride()));

  for (auto V : EV) {
    QualType QT = V->getType();
    const Type *T = QT.getTypePtrOrNull();
    if (T) {
      // Pointer to variable
      DeclRefExpr *DRE =
          DeclRefExpr::Create(AST, NestedNameSpecifierLoc(), SourceLocation(),
                              V, false, SourceLocation(), QT, VK_LValue);
      if (T->isPointerType()) {
        FuncArgs.push_back(
            ImplicitCastExpr::Create(AST, QT, CastKind::CK_LValueToRValue, DRE,
                                     nullptr, VK_PRValue, FPOptionsOverride()));
      } else {
        FuncArgs.push_back(UnaryOperator::Create(
            AST, DRE, UO_AddrOf, AST.getPointerType(QT), VK_PRValue,
            OK_Ordinary, SourceLocation(), false, FPOptionsOverride()));
      }
    }
  }

  Stmts.push_back(CreateCallExpr(AST, SourceLocation(),
                                 ArrayRef<Expr *>(FuncArgs),
                                 LibNompFuncs[NompRun]));
}

int Parser::ParseNompForClauses(std::vector<std::string> &clauses,
                                std::vector<std::string> &reductionVariables,
                                std::string &kernelName) {
  // Process auxiliary pragmas (i.e., clauses) supported after `#pragma nomp
  // for`. Mainly we want to support `annotate`, `transform` and `jit` for the
  // time being. All of the above should be parsed as an identifier token.
  bool transformDetected = 0;
  bool reductionDetected = 0;
  bool nameDetected = 0;

  // Default kernel name is "_nomp_kernel_l<line number>". If the user
  // provides a name, we will use that instead.
  FullSourceLoc Loc(Tok.getLocation(), getPreprocessor().getSourceManager());
  kernelName = "_nomp_kernel_l" + std::to_string(Loc.getSpellingLineNumber());

  while (Tok.isNot(tok::annot_pragma_nomp_end)) {
    ForClause clause = ForClauseInvalid;
    if (Tok.is(tok::identifier))
      clause = GetForClause(Tok.getIdentifierInfo()->getName());

    // Should be a valid for clause -- otherwise print error and exit.
    if (clause == ForClauseInvalid) {
      NompHandleError(diag::err_nomp_invalid_for_clause, Tok, *this,
                      Tok.getIdentifierInfo()->getName());
      return 1;
    }

    // `transform` can only be present once -- if there are two transform
    // clauses, it is an error.
    if (clause == ForClauseTransform) {
      if (transformDetected) {
        NompHandleError(diag::err_nomp_repeated_clause, Tok, *this,
                        "transform");
        return 1;
      }
      transformDetected = true;
    }

    // `reduce` can only be present once -- if there are two reduce clauses,
    // it is an error.
    if (clause == ForClauseReduce) {
      if (reductionDetected) {
        NompHandleError(diag::err_nomp_repeated_clause, Tok, *this, "reduce");
        return 1;
      }
      reductionDetected = true;
    }

    // `name` can only be present once -- if there are two name clauses,
    // it is an error.
    if (clause == ForClauseName) {
      if (nameDetected) {
        NompHandleError(diag::err_nomp_repeated_clause, Tok, *this, "name");
        return 1;
      }
      nameDetected = true;
    }

    // Consume the clause and the following "(".
    ConsumeToken();
    if (!TryConsumeToken(tok::l_paren)) {
      NompHandleError(diag::err_nomp_lparen_expected, Tok, *this,
                      ForClauses[clause]);
      return 1;
    }

    // `name` and `jit` takes a single string argument. `transform`, `annotate`
    // and `reduce should be followed by two arguments. In any case, we should
    // get a string literal next.
    // FIXME: This can be a string variable as well. Need to support that.
    if (Tok.isNot(tok::string_literal)) {
      NompHandleError(diag::err_nomp_string_literal_expected, Tok, *this);
      return 1;
    }

    // Get the string literal as a string. Consume the string literal token.
    std::string arg0;
    {
      arg0 = std::string(Tok.getLiteralData() + 1, Tok.getLength() - 2);
      ConsumeToken();
    }

    // We don't need to pass `name` clause to libnomp since we hard code the
    // kernel name in to the kernel string itself. So we are done.
    if (clause == ForClauseName) {
      kernelName = arg0;
      goto consume_r_paren;
    }

    // If the clause is not `name`, store the clause, and the string literal.
    {
      clauses.push_back(ForClauses[clause]);
      clauses.push_back(arg0);
    }

    // We are done if the clause is `jit`.
    if (clause == ForClauseJit)
      goto consume_r_paren;

    // If the clause is `reduce`, store the string literal in the
    // reductionVariables so we can easily check if a variable is part of a
    // reduction or not later.
    if (clause == ForClauseReduce)
      reductionVariables.push_back(arg0);

    // If we are handling an `annotate`, `transform` or `reduce` clause, we
    // should expect one more string literal after a comma.
    // FIXME: This can be a string variable as well. Need to support that.
    // In case of a reduction, this should be just "+" or "*" without double
    // quotations.
    if (!TryConsumeToken(tok::comma)) {
      NompHandleError(diag::err_nomp_comma_expected, Tok, *this);
      return 1;
    }
    if (Tok.isNot(tok::string_literal)) {
      NompHandleError(diag::err_nomp_string_literal_expected, Tok, *this);
      return 1;
    }

    // Get the string literal as a string. Consume the string literal token.
    {
      clauses.push_back(
          std::string(Tok.getLiteralData() + 1, Tok.getLength() - 2));
      ConsumeToken();
    }

  consume_r_paren:
    if (!TryConsumeToken(tok::r_paren)) {
      NompHandleError(diag::err_nomp_rparen_expected, Tok, *this,
                      ForClauses[clause]);
      return 1;
    }
  }

  if (!TryConsumeToken(tok::annot_pragma_nomp_end)) {
    NompHandleError(diag::err_nomp_eod_expected, Tok, *this, "for");
    return 1;
  }
  return 0;
}

StmtResult Parser::ParseNompFor(const SourceLocation &SL) {
  Sema &S = getActions();
  ASTContext &AST = S.getASTContext();

  std::vector<std::string> clauses, reductionVariables;
  std::string kernelName;
  if (ParseNompForClauses(clauses, reductionVariables, kernelName))
    return StmtEmpty();

  // Check if the next token is tok::kw_for. If not, exit.
  if (Tok.isNot(tok::kw_for)) {
    NompHandleError(diag::err_nomp_for_expected, Tok, *this, "for");
    return StmtEmpty();
  }

  // Parse the for statement
  ForStmt *FS = ParseForStatement(nullptr).getAs<ForStmt>();

  // Do some checks and preprocessing on the for statement.
  PreprocessVisitor PPV(FS);

  std::set<VarDecl *> EV;
  PPV.GetExternalVarDecls(EV);

  std::string Knl;
  GetKernel(Knl, kernelName, EV, FS, AST.getLangOpts());

  // We are going to create all our statements (declarations, function calls)
  // into the following vector and then create a compound statement out of it.
  llvm::SmallVector<Stmt *, 16> Stmts;

  // We will collect the DeclStmts in the following array.
  llvm::SmallVector<Decl *, 3> D;

  // First, let's create the statement `static int id = -1;`
  QualType IntTy = getIntType(AST);
  VarDecl *ID =
      VarDecl::Create(AST, S.CurContext, SL, SL, &AST.Idents.get("id"), IntTy,
                      AST.getTrivialTypeSourceInfo(IntTy), SC_Static);
  UnaryOperator *M1 = UnaryOperator::Create(
      AST, IntegerLiteral::Create(AST, llvm::APInt(32, 1), IntTy, SL), UO_Minus,
      IntTy, VK_PRValue, OK_Ordinary, SL, false, FPOptionsOverride());
  ID->setInit(M1);
  D.push_back(ID);
  Stmts.push_back(
      new (AST) DeclStmt(DeclGroupRef::Create(AST, D.begin(), 1), SL, SL));

  QualType ConstCharTy = AST.getConstType(AST.CharTy);
  QualType ConstStringTy = AST.getPointerType(ConstCharTy);

  // We will create `const char knl[K] = "..."` variable to hold the kernel
  D.clear();
  QualType KnlStrTy =
      getConstantArrayType(AST, ConstCharTy, Knl.size() + 1, ArrayType::Normal);
  VarDecl *VKnl = VarDecl::Create(
      AST, S.CurContext, SL, SL, &AST.Idents.get("knl"), KnlStrTy,
      AST.getTrivialTypeSourceInfo(KnlStrTy), SC_None);
  StringLiteral *KSL = StringLiteral::Create(AST, Knl, StringLiteral::Ordinary,
                                             false, KnlStrTy, SL);
  ImplicitCastExpr *ICE =
      ImplicitCastExpr::Create(AST, ConstStringTy, CastKind::CK_LValueToRValue,
                               KSL, nullptr, VK_PRValue, FPOptionsOverride());
  VKnl->setInit(ICE);
  D.push_back(VKnl);
  Stmts.push_back(
      new (AST) DeclStmt(DeclGroupRef::Create(AST, D.begin(), 1), SL, SL));

  // Next we create the decl for `const char *clauses[N] = {...}
  D.clear();
  QualType ClausesStrTy = getConstantArrayType(
      AST, ConstStringTy, clauses.size() + 1, ArrayType::Normal);
  VarDecl *CLS = VarDecl::Create(
      AST, S.CurContext, SL, SL, &AST.Idents.get("clauses"), ClausesStrTy,
      AST.getTrivialTypeSourceInfo(ClausesStrTy), SC_None);

  QualType StringTy = AST.getPointerType(AST.CharTy);
  llvm::SmallVector<Expr *, 16> InitList;
  for (auto cls : clauses) {
    QualType ClauseTy = getConstantArrayType(AST, AST.CharTy, cls.size() + 1,
                                             ArrayType::Normal);
    StringLiteral *L = StringLiteral::Create(
        AST, cls, StringLiteral::StringKind::Ordinary, false, ClauseTy, SL);
    ImplicitCastExpr *ICE0 =
        ImplicitCastExpr::Create(AST, StringTy, CK_ArrayToPointerDecay, L,
                                 nullptr, VK_PRValue, FPOptionsOverride());
    ImplicitCastExpr *ICE1 =
        ImplicitCastExpr::Create(AST, ConstStringTy, CK_NoOp, ICE0, nullptr,
                                 VK_PRValue, FPOptionsOverride());
    InitList.push_back(ICE1);
  }

  IntegerLiteral *Zero =
      IntegerLiteral::Create(AST, llvm::APInt(32, 0), IntTy, SL);
  ImplicitCastExpr *ICEZ =
      ImplicitCastExpr::Create(AST, ConstStringTy, CK_NullToPointer, Zero,
                               nullptr, VK_PRValue, FPOptionsOverride());
  InitList.push_back(ICEZ);

  Expr *ILE = new (AST) InitListExpr(AST, SL, ArrayRef<Expr *>(InitList), SL);
  ILE->setType(ClausesStrTy);
  CLS->setInit(ILE);

  D.push_back(CLS);

  Stmts.push_back(
      new (AST) DeclStmt(DeclGroupRef::Create(AST, D.begin(), 1), SL, SL));

  // Next we create the AST node for the function call nomp_jit(). To do that
  // we create the function arguments to nomp_jit().
  CreateNompJitCall(Stmts, AST, ID, VKnl, CLS, EV, reductionVariables);

  // Next we create AST node for nomp_run().
  CreateNompRunCall(Stmts, AST, ID, EV);

  return CompoundStmt::Create(AST, ArrayRef<Stmt *>(Stmts), FPOptionsOverride(),
                              SL, SL);
}

StmtResult Parser::ParseNompSync(const SourceLocation &SL) {
  ASTContext &AST = getActions().getASTContext();

  if (!TryConsumeToken(tok::annot_pragma_nomp_end)) {
    NompHandleError(diag::err_nomp_eod_expected, Tok, *this, "finalize");
    return StmtEmpty();
  }

  return CreateCallExpr(AST, SL, ArrayRef<Expr *>(), LibNompFuncs[NompSync]);
}

StmtResult Parser::ParseNompFinalize(const SourceLocation &SL) {
  ASTContext &AST = getActions().getASTContext();

  if (!TryConsumeToken(tok::annot_pragma_nomp_end)) {
    NompHandleError(diag::err_nomp_eod_expected, Tok, *this, "finalize");
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
//       for-directive:
//         annot_pragma_nomp 'for'
//         annot_pragma_nomp_end
//
StmtResult Parser::ParseNompDirective(ParsedStmtContext StmtCtx) {
  // Fill the libnomp function declaration array: LibNompFuncs
  Sema &S = getActions();
  FindLibNompFunctionDecl("nomp_init", S);
  FindLibNompFunctionDecl("nomp_update", S);
  FindLibNompFunctionDecl("nomp_jit", S);
  FindLibNompFunctionDecl("nomp_run", S);
  FindLibNompFunctionDecl("nomp_sync", S);
  FindLibNompFunctionDecl("nomp_finalize", S);

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
  case DirectiveSync:
    result = ParseNompSync(SL);
    break;
  case DirectiveInvalid:
    NompHandleError(diag::err_nomp_invalid_directive, Tok, *this);
    break;
  }

  return result;
}
