#include "clang/AST/Decl.h"
#include "clang/AST/Expr.h"
#include "clang/AST/Stmt.h"
#include "clang/Lex/Preprocessor.h"
#include "clang/Lex/Token.h"
#include "clang/Parse/ParseDiagnostic.h"
#include "clang/Parse/Parser.h"
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

StmtResult ParseNompInit(Parser &p, Token &tok, const SourceLocation &sLoc) {
  Preprocessor &pp = p.getPreprocessor();
  SourceManager &sm = pp.getSourceManager();
  Sema &sema = p.getActions();
  ASTContext &ast = sema.getASTContext();

  pp.Lex(tok);

  if (tok.isNot(tok::l_paren)) {
    FullSourceLoc loc(tok.getLocation(), sm);
    pp.Diag(tok, diag::err_nomp_lparen_expected)
        << "init" << loc.getLineNumber();
  }

  while (tok.isNot(tok::annot_pragma_nomp_end))
    pp.Lex(tok);

  // if (tok.isNot(tok::annot_pragma_nomp_end)) {
  //   FullSourceLoc loc(tok.getLocation(), sm);
  //   pp.Diag(tok, diag::err_nomp_rparen_expected) << loc.getLineNumber();
  // }

  FunctionDecl *FD = NompFuncDecls[NompInit];
  QualType QT = FD->getType();
  DeclRefExpr *DRE = DeclRefExpr::Create(
      ast, NestedNameSpecifierLoc(), SourceLocation(), FD, false, sLoc,
      FD->getType(), ExprValueKind::VK_PRValue);

  QualType PQT = ast.getPointerType(QT);
  ImplicitCastExpr *ICE = ImplicitCastExpr::Create(
      ast, PQT, CastKind::CK_FunctionToPointerDecay, DRE, nullptr,
      ExprValueKind::VK_PRValue, FPOptionsOverride());

  return CallExpr::Create(ast, ICE, {}, FD->getCallResultType(),
                          ExprValueKind::VK_PRValue, sLoc, FPOptionsOverride());
}

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

/// Parsing of NOMP directives.
///
///       init-directive:
///         annot_pragma_nomp 'init' simple-variable-list
///         annot_pragma_nomp_end
///       update-directive:
///         annot_pragma_nomp 'update' direction simple-variable-list
///         annot_pragma_nomp_end
///
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
    result = ParseNompInit(*this, Tok, sLoc);
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

  if (Tok.isNot(tok::annot_pragma_nomp_end)) {
    std::cout << "OOps error\n";
  }
  PP.Lex(Tok);

  return result;
}
