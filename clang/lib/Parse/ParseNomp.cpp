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

//==============================================================================
// Helper functions
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

// static Expr *ParseNompInitArg(Token &tok, const Parser &p) {
//   Preprocessor &pp = p.getPreprocessor();
//   SourceManager &sm = pp.getSourceManager();
//   Sema &sema = p.getActions();
//   ASTContext &ctx = sema.getASTContext();
//
//   DeclContext::lookup_result result;
//   DeclRefExpr *DRE;
//
//   FullSourceLoc loc(tok.getLocation(), sm);
//   tok::TokenKind TK = tok.getKind();
//   switch (TK) {
//   case tok::numeric_constant:
//     uint64_t val;
//     if (pp.parseSimpleIntegerLiteral(tok, val))
//       return IntegerLiteral::Create(ctx, llvm::APInt(32, val), ctx.IntTy,
//                                     tok.getLocation());
//     pp.Diag(tok, diag::err_nomp_integer_literal_expected)
//         << loc.getLineNumber() << loc.getColumnNumber();
//     break;
//   case tok::identifier:
//     // Check for the declation of the identifier in current FunctionDecl.
//     // If not found, check on the translationUnitDecl. If not found in
//     either,
//     // it's an error.
//     result = sema.getFunctionLevelDeclContext()->lookup(
//         DeclarationName(tok.getIdentifierInfo()));
//     if (result.empty())
//       result = ctx.getTranslationUnitDecl()->lookup(
//           DeclarationName(tok.getIdentifierInfo()));
//     if (!result.empty()) {
//       if (result.isSingleResult()) {
//         VarDecl *VD = result.find_first<VarDecl>();
//         DRE = DeclRefExpr::Create(
//             ctx, NestedNameSpecifierLoc(), SourceLocation(), VD, false,
//             tok.getLocation(), VD->getType(), ExprValueKind::VK_PRValue);
//         pp.Lex(tok);
//         return ImplicitCastExpr::Create(
//             ctx, VD->getType(), CastKind::CK_LValueToRValue, DRE, nullptr,
//             ExprValueKind::VK_PRValue, FPOptionsOverride());
//       } else {
//         // Error ! Don't know what to do !
//         std::cout << "Don't know what to do !\n";
//       }
//     }
//     std::cout << "Token not found !\n";
//     // Error ! Not found !
//     break;
//   case tok::comma:
//   case tok::r_paren:
//     break;
//   default:
//     pp.Diag(tok, diag::err_nomp_invalid_token)
//         << loc.getLineNumber() << loc.getColumnNumber();
//     break;
//   }
//   pp.Lex(tok);
//   return nullptr;
// }

//==============================================================================
// Helper functions
//
StmtResult Parser::ParseNompInit(SourceLocation &SL) {
  Preprocessor &pp = getPreprocessor();
  SourceManager &sm = pp.getSourceManager();
  Sema &sema = getActions();
  ASTContext &ast = sema.getASTContext();

  pp.Lex(Tok);
  if (Tok.isNot(tok::l_paren)) {
    FullSourceLoc loc(Tok.getLocation(), sm);
    pp.Diag(Tok, diag::err_nomp_lparen_expected)
        << "init" << loc.getLineNumber() << loc.getColumnNumber();
  }
  ConsumeToken();

  llvm::SmallVector<Expr *, 16> ExprArgs;
  ExprResult ER = ParseExpression();
  if (ER.isUsable()) {
    Expr *E = ER.getAs<Expr>();
    // TODO: Check if the binary operator is the comma operator
    if (BinaryOperator *BO = dyn_cast<BinaryOperator>(E)) {
      // LHS it self must be a binary operator
      if (BinaryOperator *LHS = dyn_cast<BinaryOperator>(BO->getLHS())) {
        ExprArgs.push_back(LHS->getLHS());
        ExprArgs.push_back(LHS->getRHS());
      } else {
        // TODO: Error
      }
      ExprArgs.push_back(BO->getRHS());
    } else {
      // TODO: Error
    }
  }

  if (Tok.isNot(tok::r_paren)) {
    FullSourceLoc loc(Tok.getLocation(), sm);
    pp.Diag(Tok, diag::err_nomp_rparen_expected)
        << "init" << loc.getLineNumber() << loc.getColumnNumber();
  }
  ConsumeToken();
  ConsumeAnnotationToken();

  FunctionDecl *FD = NompFuncDecls[NompInit];
  QualType QT = FD->getType();
  DeclRefExpr *DRE =
      DeclRefExpr::Create(ast, NestedNameSpecifierLoc(), SourceLocation(), FD,
                          false, SL, FD->getType(), ExprValueKind::VK_PRValue);

  QualType PQT = ast.getPointerType(QT);
  ImplicitCastExpr *ICE = ImplicitCastExpr::Create(
      ast, PQT, CastKind::CK_FunctionToPointerDecay, DRE, nullptr,
      ExprValueKind::VK_PRValue, FPOptionsOverride());

  return CallExpr::Create(ast, ICE, ArrayRef<Expr *>(ExprArgs),
                          FD->getCallResultType(), ExprValueKind::VK_PRValue,
                          SL, FPOptionsOverride());
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
    TranslationUnitDecl *tuDecl = ast.getTranslationUnitDecl();
    DeclContext *dCtx = tuDecl->castToDeclContext(tuDecl);
    for (auto d = dCtx->decls_begin(); d != dCtx->decls_end(); d++) {
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

  SourceLocation sLoc = Tok.getLocation();
  NompDirectiveKind directive = NompInvalid;
  pp.Lex(Tok);
  if (Tok.is(tok::identifier))
    directive = GetNompDirectiveKind(Tok.getIdentifierInfo()->getName());

  if (directive == NompInvalid) {
    FullSourceLoc loc(Tok.getLocation(), sm);
    pp.Diag(Tok, diag::err_nomp_invalid_directive) << loc.getLineNumber();
  }

  StmtResult result = StmtEmpty();
  switch (directive) {
  case NompInit:
    result = ParseNompInit(sLoc);
    break;
  case NompUpdate:
    break;
  case NompFor:
    break;
  case NompFinalize:
    break;
  case NompInvalid:
    break;
  }

  return result;
}
