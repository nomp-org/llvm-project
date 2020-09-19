#ifndef _OPENMPPP_CODEGEN_H_
#define _OPENMPPP_CODEGEN_H_

#include "clang/AST/Stmt.h"
#include "clang/AST/StmtVisitor.h"
#include "clang/AST/ASTContext.h"

class CodeGen {
  public:
    CodeGen(clang::ASTContext &Context, std::string Backend, std::string EndStmt);

    virtual void clearCode();
    virtual std::string stmtToString(clang::Stmt *Stmt);
    virtual void genCode(clang::Stmt *Stmt);
    std::string getCode();

    virtual std::string genForInit(clang::Stmt *ForInit, clang::VarDecl *IterVar) = 0;
    virtual std::string genKernelArgs(std::set<clang::VarDecl *> &s) = 0;
    virtual std::string genIf(clang::Stmt *Cond, clang::Stmt *Then, clang::Stmt *Else) = 0;

  protected:
    clang::ASTContext &Context;
    std::string Backend;
    std::string Code;
    std::string EndStmt;
};

class OpenCLCodeGen : public CodeGen {
  public:
    OpenCLCodeGen(clang::ASTContext &Context);

    virtual void genCode(clang::Stmt *Stmt) override;

    virtual std::string genForInit(clang::Stmt *ForInit, clang::VarDecl *IterVar) override;
    virtual std::string genKernelArgs(std::set<clang::VarDecl *> &s) override;
    virtual std::string genIf(clang::Stmt *Cond, clang::Stmt *Then, clang::Stmt *Else) override;
};

#endif
