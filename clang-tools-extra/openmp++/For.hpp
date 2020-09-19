#ifndef _OPENMPPP_FOR_H_
#define _OPENMPPP_FOR_H_

#include "clang/AST/StmtVisitor.h"

#include "clang/Frontend/CompilerInstance.h"

#include "CodeGen.hpp"

class ForVisitor : public clang::StmtVisitor<ForVisitor,bool> {
  public:
    ForVisitor();

    std::set<clang::VarDecl *> getVarDecls(clang::Stmt *Stmt);
    std::set<clang::DeclRefExpr *> getDeclRefExprs(clang::Stmt *Stmt);

    virtual bool VisitBinaryOperator(clang::BinaryOperator *BinaryOperator);
    virtual bool VisitDeclStmt(clang::DeclStmt *DeclStatement);
    virtual bool VisitVarDecl(clang::VarDecl *VarDecl);
    virtual bool VisitDeclRefExpr(clang::DeclRefExpr *DclRfExpr);
    virtual bool VisitImplicitCastExpr(clang::ImplicitCastExpr *ImplctCastExpr);
    virtual bool VisitUnaryOperator(clang::UnaryOperator *UnaryOperator);
    virtual bool VisitForStmt(clang::ForStmt *ForStmt);
    virtual bool VisitCompoundStmt(clang::CompoundStmt *CompoundStmt);
    virtual bool VisitArraySubscriptExpr(clang::ArraySubscriptExpr *ArraySubscriptExpr);

  protected:
    std::set<clang::VarDecl *> VarDecl;
    std::set<clang::DeclRefExpr *> DeclRefExpr;
};

#endif
