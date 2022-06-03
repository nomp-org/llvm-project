#include "clang/Lex/Preprocessor.h"
#include "clang/Lex/Token.h"
#include "clang/Parse/Parser.h"
#include "llvm/ADT/StringSwitch.h"

#define MAX_CLAUSE_SIZE 32

using namespace clang;

static Token parseUpdate(Preprocessor &PP,
                         SmallVector<Token, MAX_CLAUSE_SIZE> &Pragma) {
  Token tok;
  PP.Lex(tok); // l_paren

  PP.Lex(tok); // identifier (direction)
  IdentifierInfo *Direction = tok.getIdentifierInfo();
  bool valid = llvm::StringSwitch<bool>(Direction->getName())
                   .Case("to", true)
                   .Case("from", true)
                   .Case("tofrom", true)
                   .Case("alloc", true)
                   .Case("free", true)
                   .Default(false);
  if (!valid) {
    llvm::outs() << "Update: Invalid Direction !\n";
    return tok;
  }

  PP.Lex(tok); // colon
  llvm::outs() << "Update: " << tok.getName() << '\n';

  do {
    PP.Lex(tok);
    llvm::outs() << "Update: " << tok.getName() << '\n';
  } while (tok.isNot(tok::r_paren));

  PP.Lex(tok);
  return tok;
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
StmtResult Parser::ParseNOMPDirective(ParsedStmtContext StmtCtx) {
  assert(Tok.is(tok::annot_pragma_nomp));

  Preprocessor& pp = getPreprocessor();
  SourceManager& sm = pp.getSourceManager();
  FullSourceLoc loc(Tok.getLocation(), sm);
  llvm::outs() << "Found nomp pragma on line: " << loc.getLineNumber() << "\n";

  while (Tok.isNot(tok::annot_pragma_nomp_end)) {
    ConsumeAnnotationToken();
  }
  assert(Tok.is(tok::annot_pragma_nomp_end));
  ConsumeAnnotationToken();

  return StmtEmpty();
}

#undef MAX_CLAUSE_SIZE
