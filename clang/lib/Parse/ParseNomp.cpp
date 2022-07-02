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
#include "clang/Lex/Preprocessor.h"
#include "clang/Lex/Token.h"
#include "clang/Parse/ParseDiagnostic.h"
#include "clang/Parse/Parser.h"
#include "clang/Sema/Ownership.h"
#include "clang/Sema/Sema.h"
#include "llvm/ADT/StringSwitch.h"

#include <iostream>

using namespace clang;

static const int maxNompFuncDecls = 4;
static FunctionDecl *NompFuncDecls[maxNompFuncDecls] = {nullptr};
static int numNompFuncDecls = 0;

enum NompDirectiveKind {
  NompInvalid = -1,
  NompInit = 0,
  NompUpdate = 1,
  NompFor = 2,
  NompFinalize = 3
};

enum NompUpdateDirection {
  NompUpdateInvalid = -1,
  NompUpdateTo = 0,
  NompUpdateFrom = 1,
  NompUpdateAlloc = 2,
  NompUpdateFree = 3
};

//==============================================================================
// Helper functions: String to Nomp types conversion
//
static inline NompDirectiveKind
GetNompDirectiveKind(const llvm::StringRef name) {
  return llvm::StringSwitch<NompDirectiveKind>(name)
      .Case("init", NompInit)
      .Case("update", NompUpdate)
      .Case("for", NompFor)
      .Case("finalize", NompFinalize)
      .Default(NompInvalid);
}

static inline NompDirectiveKind
GetNompFuncDeclKind(const llvm::StringRef name) {
  return llvm::StringSwitch<NompDirectiveKind>(name)
      .Case("nomp_init", NompInit)
      .Case("nomp_update", NompUpdate)
      .Case("nomp_for", NompFor)
      .Case("nomp_finalize", NompFinalize)
      .Default(NompInvalid);
}

static inline NompUpdateDirection
GetNompUpdateDirection(const llvm::StringRef dirn) {
  return llvm::StringSwitch<NompUpdateDirection>(dirn)
      .Case("to", NompUpdateTo)
      .Case("from", NompUpdateFrom)
      .Case("alloc", NompUpdateAlloc)
      .Case("free", NompUpdateFree)
      .Default(NompUpdateInvalid);
}

//==============================================================================
// Helper functions: Tokens to Clang Stmt conversions
//
static bool GetVariableAsFuncArg(ImplicitCastExpr *&ICE, VarDecl *&VD,
                                 Token &tok, Parser &p) {
  Preprocessor &pp = p.getPreprocessor();
  SourceManager &sm = pp.getSourceManager();
  Sema &sema = p.getActions();
  ASTContext &ast = sema.getASTContext();

  FullSourceLoc loc(tok.getLocation(), sm);
  tok::TokenKind TK = tok.getKind();
  if (TK != tok::identifier) {
    // If the token is not an identifier, it is an error
    pp.Diag(tok, diag::err_nomp_identifier_expected)
        << loc.getLineNumber() << loc.getColumnNumber();
    p.SkipUntil(tok::annot_pragma_nomp_end);
  } else {
    // Check for the declation of the identifier in current scope and
    // If not found, check on the translation Unit scope. If not found
    // in thre either, it's an error.
    DeclarationName DN = DeclarationName(tok.getIdentifierInfo());
    VD = dyn_cast_or_null<VarDecl>(
        sema.LookupSingleName(p.getCurScope(), DN, SourceLocation(),
                              Sema::LookupNameKind::LookupOrdinaryName));
    if (!VD)
      VD = dyn_cast_or_null<VarDecl>(
          sema.LookupSingleName(sema.TUScope, DN, SourceLocation(),
                                Sema::LookupNameKind::LookupOrdinaryName));

    if (VD) {
      DeclRefExpr *DRE = DeclRefExpr::Create(
          ast, NestedNameSpecifierLoc(), SourceLocation(), VD, false,
          tok.getLocation(), VD->getType(), ExprValueKind::VK_PRValue);
      ICE = ImplicitCastExpr::Create(
          ast, VD->getType(), CastKind::CK_LValueToRValue, DRE, nullptr,
          ExprValueKind::VK_PRValue, FPOptionsOverride());
      return true;
    }

    // Variable declaration not found
    pp.Diag(tok, diag::err_nomp_no_vardecl_found)
        << DN.getAsString() << loc.getLineNumber() << loc.getColumnNumber();
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

int Parser::ParseNompExpr(llvm::SmallVector<Expr *, 16> &ExprList) {
  ExprResult LHS = ParseAssignmentExpression();
  ExprResult ER = ParseRHSOfBinaryExpression(LHS, prec::Assignment);
  if (ER.isUsable()) {
    ExprList.push_back(ER.getAs<Expr>());
    return 0;
  }
  return 1;
}

void Parser::ParseNompExprListUntilRParen(
    llvm::SmallVector<Expr *, 16> &ExprList, llvm::StringRef Pragma) {
  Preprocessor &pp = getPreprocessor();
  SourceManager &sm = pp.getSourceManager();

  while (Tok.isNot(tok::r_paren) and Tok.isNot(tok::annot_pragma_nomp_end)) {
    ParseNompExpr(ExprList);
    if (Tok.isNot(tok::r_paren)) {
      if (!TryConsumeToken(tok::comma)) {
        FullSourceLoc loc(Tok.getLocation(), sm);
        pp.Diag(Tok, diag::err_nomp_comma_expected)
            << Pragma << loc.getLineNumber() << loc.getColumnNumber();
        SkipUntil(tok::annot_pragma_nomp_end);
      }
    }
  }

  if (!TryConsumeToken(tok::r_paren)) {
    FullSourceLoc loc(Tok.getLocation(), sm);
    pp.Diag(Tok, diag::err_nomp_rparen_expected)
        << Pragma << loc.getLineNumber() << loc.getColumnNumber();
    SkipUntil(tok::annot_pragma_nomp_end);
  }
}

//==============================================================================
// Parse and generate calls for Nomp API functions
//
StmtResult Parser::ParseNompInit(const SourceLocation &SL) {
  Preprocessor &pp = getPreprocessor();
  SourceManager &sm = pp.getSourceManager();
  Sema &sema = getActions();
  ASTContext &ast = sema.getASTContext();

  // "("
  if (!TryConsumeToken(tok::l_paren)) {
    FullSourceLoc loc(Tok.getLocation(), sm);
    pp.Diag(Tok, diag::err_nomp_lparen_expected)
        << "init" << loc.getLineNumber() << loc.getColumnNumber();
    SkipUntil(tok::annot_pragma_nomp_end);
    return StmtEmpty();
  }

  llvm::SmallVector<Expr *, 16> CallArgs;
  ParseNompExprListUntilRParen(CallArgs, "init");
  ConsumeAnnotationToken(); // tok::annot_pragma_nomp_end

  if (CallArgs.size() != 3) {
    FullSourceLoc loc(SL, sm);
    pp.Diag(Tok, diag::err_nomp_invalid_number_of_args)
        << CallArgs.size() << "init" << 3 << loc.getLineNumber();
    SkipUntil(tok::annot_pragma_nomp_end);
    return StmtEmpty();
  }

  return CreateCallExpr(ast, SL, ArrayRef<Expr *>(CallArgs),
                        NompFuncDecls[NompInit]);
}

StmtResult Parser::ParseNompUpdate(const SourceLocation &SL) {
  Preprocessor &PP = getPreprocessor();
  SourceManager &SM = PP.getSourceManager();
  ASTContext &AST = getActions().getASTContext();

  // "("
  if (!TryConsumeToken(tok::l_paren)) {
    FullSourceLoc loc(Tok.getLocation(), SM);
    PP.Diag(Tok, diag::err_nomp_lparen_expected)
        << "update" << loc.getLineNumber() << loc.getColumnNumber();
    SkipUntil(tok::annot_pragma_nomp_end);
    return StmtEmpty();
  }

  // Direction: "to", "from", "alloc", "free"
  NompUpdateDirection dirn = NompUpdateInvalid;
  if (Tok.is(tok::identifier))
    dirn = GetNompUpdateDirection(Tok.getIdentifierInfo()->getName());

  if (dirn == NompUpdateInvalid) {
    FullSourceLoc loc(Tok.getLocation(), SM);
    PP.Diag(Tok, diag::err_nomp_invalid_update_direction)
        << loc.getLineNumber() << loc.getColumnNumber();
    SkipUntil(tok::annot_pragma_nomp_end);
    return StmtEmpty();
  } else {
    ConsumeToken();
  }

  // ":"
  if (!TryConsumeToken(tok::colon)) {
    FullSourceLoc loc(Tok.getLocation(), SM);
    PP.Diag(Tok, diag::err_nomp_colon_expected)
        << "update" << loc.getLineNumber() << loc.getColumnNumber();
    SkipUntil(tok::annot_pragma_nomp_end);
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
    if (!GetVariableAsFuncArg(ICE, VD, Tok, *this)) {
      SkipUntil(tok::annot_pragma_nomp_end);
      return StmtEmpty();
    }
    const Type *T = ICE->getType().getTypePtr();
    if (!T->isPointerType()) {
      FullSourceLoc loc(Tok.getLocation(), SM);
      PP.Diag(Tok, diag::err_nomp_pointer_type_expected)
          << "update" << loc.getLineNumber() << loc.getColumnNumber();
      SkipUntil(tok::annot_pragma_nomp_end);
      return StmtEmpty();
    }
    ConsumeToken();
    FuncArgs.push_back(ICE);

    // Start offset
    if (!TryConsumeToken(tok::l_square)) {
      FullSourceLoc loc(Tok.getLocation(), SM);
      PP.Diag(Tok, diag::err_nomp_lsquare_expected)
          << "update" << loc.getLineNumber() << loc.getColumnNumber();
      SkipUntil(tok::annot_pragma_nomp_end);
      return StmtEmpty();
    }
    ParseNompExpr(FuncArgs);

    // End offset
    if (!TryConsumeToken(tok::comma)) {
      FullSourceLoc loc(Tok.getLocation(), SM);
      PP.Diag(Tok, diag::err_nomp_comma_expected)
          << "update" << loc.getLineNumber() << loc.getColumnNumber();
      SkipUntil(tok::annot_pragma_nomp_end);
      return StmtEmpty();
    }
    ParseNompExpr(FuncArgs);

    if (!TryConsumeToken(tok::r_square)) {
      FullSourceLoc loc(Tok.getLocation(), SM);
      PP.Diag(Tok, diag::err_nomp_rsquare_expected)
          << "update" << loc.getLineNumber() << loc.getColumnNumber();
      SkipUntil(tok::annot_pragma_nomp_end);
      return StmtEmpty();
    }

    // sizeof()
    QualType CT = T->getPointeeOrArrayElementType()->getCanonicalTypeInternal();
    UnaryExprOrTypeTraitExpr *UETT = new (AST) UnaryExprOrTypeTraitExpr(
        UETT_SizeOf, AST.getTrivialTypeSourceInfo(CT), AST.getSizeType(),
        SourceLocation(), SourceLocation());
    FuncArgs.push_back(UETT);
    FuncCalls.push_back(
        CreateCallExpr(AST, TL, FuncArgs, NompFuncDecls[NompUpdate]));
    TryConsumeToken(tok::comma);
  }

  if (!TryConsumeToken(tok::r_paren)) {
    FullSourceLoc loc(Tok.getLocation(), SM);
    PP.Diag(Tok, diag::err_nomp_rparen_expected)
        << "update" << loc.getLineNumber() << loc.getColumnNumber();
    SkipUntil(tok::annot_pragma_nomp_end);
    return StmtEmpty();
  }

  SourceLocation EL = Tok.getLocation();
  SkipUntil(tok::annot_pragma_nomp_end);
  return CompoundStmt::Create(AST, ArrayRef<Stmt *>(FuncCalls), SL, EL);
}

StmtResult Parser::ParseNompFinalize(const SourceLocation &SL) {
  Preprocessor &pp = getPreprocessor();
  SourceManager &sm = pp.getSourceManager();
  Sema &sema = getActions();
  ASTContext &ast = sema.getASTContext();

  if (!TryConsumeToken(tok::annot_pragma_nomp_end)) {
    FullSourceLoc loc(Tok.getLocation(), sm);
    pp.Diag(Tok, diag::err_nomp_eod_expected)
        << "finalize" << loc.getLineNumber() << loc.getColumnNumber();
    return StmtEmpty();
  }

  return CreateCallExpr(ast, SL, ArrayRef<Expr *>(),
                        NompFuncDecls[NompFinalize]);
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
  assert(Tok.is(tok::annot_pragma_nomp));
  Preprocessor &pp = this->getPreprocessor();
  SourceManager &sm = pp.getSourceManager();

  if (numNompFuncDecls == 0) {
    ASTContext &ast = this->getActions().getASTContext();
    TranslationUnitDecl *TUD = ast.getTranslationUnitDecl();
    DeclContext *DC = TUD->castToDeclContext(TUD);
    for (auto d = DC->decls_begin(); d != DC->decls_end(); d++) {
      if (FunctionDecl *decl = dyn_cast<FunctionDecl>(*d)) {
        NompDirectiveKind directive =
            GetNompFuncDeclKind(decl->getNameInfo().getAsString());
        if (directive != NompInvalid) {
          NompFuncDecls[directive] = decl;
          numNompFuncDecls++;
        }
      }
    }
  }

  SourceLocation SL = Tok.getLocation();
  NompDirectiveKind directive = NompInvalid;
  pp.Lex(Tok);
  if (Tok.is(tok::identifier))
    directive = GetNompDirectiveKind(Tok.getIdentifierInfo()->getName());

  if (directive == NompInvalid) {
    FullSourceLoc loc(Tok.getLocation(), sm);
    pp.Diag(Tok, diag::err_nomp_invalid_directive) << loc.getLineNumber();
  } else {
    ConsumeToken();
  }

  StmtResult result = StmtEmpty();
  switch (directive) {
  case NompInit:
    result = ParseNompInit(SL);
    break;
  case NompUpdate:
    result = ParseNompUpdate(SL);
    break;
  case NompFor:
    break;
  case NompFinalize:
    result = ParseNompFinalize(SL);
    break;
  case NompInvalid:
    break;
  }

  return result;
}
