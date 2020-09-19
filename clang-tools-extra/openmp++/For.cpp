#include "For.hpp"

#include <iostream>

ForVisitor::ForVisitor() {}

std::set<clang::VarDecl *> ForVisitor::getVarDecls(clang::Stmt *Stmt) {
  VarDecl.clear();
  StmtVisitor::Visit(Stmt);

  return VarDecl;
}

std::set<clang::DeclRefExpr *> ForVisitor::getDeclRefExprs(clang::Stmt *Stmt) {
  DeclRefExpr.clear();
  StmtVisitor::Visit(Stmt);

  return DeclRefExpr;
}

bool ForVisitor::VisitBinaryOperator(clang::BinaryOperator *BinaryOp) {
  StmtVisitor::Visit(BinaryOp->getLHS());
  StmtVisitor::Visit(BinaryOp->getRHS());

  return true;
}

bool ForVisitor::VisitDeclRefExpr(clang::DeclRefExpr *DeclRefExpression) {
  DeclRefExpr.insert(DeclRefExpression);

  return true;
}

bool ForVisitor::VisitDeclStmt(clang::DeclStmt *DeclStatement) {
  for (auto it = DeclStatement->decl_begin(); it != DeclStatement->decl_end(); it++) {
    if (auto Var = llvm::dyn_cast_or_null<clang::VarDecl>(*it)) {
      StmtVisitor::Visit(Var->getInit());
      VarDecl.insert(Var);
    }
  }

  return true;
}

bool ForVisitor::VisitVarDecl(clang::VarDecl *VarDecl) {
  return true;
}

bool ForVisitor::VisitImplicitCastExpr(clang::ImplicitCastExpr *ImplctCastExpr) {
  clang::Expr *SubExpr = ImplctCastExpr->getSubExpr();
  StmtVisitor::Visit(SubExpr);

  return true;
}

bool ForVisitor::VisitUnaryOperator(clang::UnaryOperator *UnaryOp) {
  clang::Expr *Decl=UnaryOp->getSubExpr();
  if (auto Var = llvm::dyn_cast_or_null<clang::DeclRefExpr>(Decl)) {
    StmtVisitor::Visit(Var);
  }

  return true;
}

bool ForVisitor::VisitForStmt(clang::ForStmt *ForStmt) {
  StmtVisitor::Visit(ForStmt->getInit());
  StmtVisitor::Visit(ForStmt->getCond());
  StmtVisitor::Visit(ForStmt->getInc());
  StmtVisitor::Visit(ForStmt->getBody());

  return true;
}

bool ForVisitor::VisitCompoundStmt(clang::CompoundStmt *CompoundStmt) {
  for (auto it = CompoundStmt->body_begin(); it != CompoundStmt->body_end(); it++) {
    StmtVisitor::Visit(*it);
  }

  return true;
}

bool ForVisitor::VisitArraySubscriptExpr(clang::ArraySubscriptExpr *ArraySubscriptExpr) {
  StmtVisitor::Visit(ArraySubscriptExpr->getLHS());
  StmtVisitor::Visit(ArraySubscriptExpr->getRHS());

  return true;
}
