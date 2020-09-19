#include <iostream>
#include <vector>
#include <set>

#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/AST/ASTConsumer.h"
#include "clang/Frontend/FrontendAction.h"
#include "clang/Frontend/CompilerInstance.h"
#include "clang/Tooling/Tooling.h"

#include "llvm/Support/Casting.h"

#include "CodeGen.hpp"
#include "For.hpp"

class FindForClassVisitor: public clang::RecursiveASTVisitor<FindForClassVisitor> {
  public:
    FindForClassVisitor(clang::ASTContext &Context_,std::shared_ptr<CodeGen> &CodeGenerator_)
      : Context(Context_), CodeGenerator(CodeGenerator_) {}

    clang::VarDecl *FindIterVar(clang::ForStmt *ForStatement) {
      ForVisitor Visitor;

      clang::Stmt *Init = ForStatement->getInit();
      std::set<clang::VarDecl *> InitVars;
      std::set<clang::DeclRefExpr *> Decls;
      if (Init != nullptr) {
        InitVars = Visitor.getVarDecls(Init);
        Decls = Visitor.getDeclRefExprs(Init);
      }
      for (auto it = Decls.begin(); it != Decls.end(); it++) {
        clang::VarDecl *Var = llvm::dyn_cast_or_null<clang::VarDecl>((*it)->getDecl());
        if (Var != nullptr) 
          InitVars.insert(Var);
      }

      clang::Stmt *Cond = ForStatement->getCond();
      std::set<clang::VarDecl *> CondVars;
      if (Cond != nullptr) {
        CondVars = Visitor.getVarDecls(Cond);
        Decls = Visitor.getDeclRefExprs(Cond);
      }
      for (auto it = Decls.begin(); it != Decls.end(); it++) {
        clang::VarDecl *Var = llvm::dyn_cast_or_null<clang::VarDecl>((*it)->getDecl());
        if (Var != nullptr) 
          CondVars.insert(Var);
      }

      clang::Stmt *Inc = ForStatement->getInc();
      std::set<clang::VarDecl *> IncVars;
      if (Inc != nullptr) {
        IncVars = Visitor.getVarDecls(Inc);
        Decls = Visitor.getDeclRefExprs(Inc);
      }
      for (auto it = Decls.begin(); it != Decls.end(); it++) {
        clang::VarDecl *Var = llvm::dyn_cast_or_null<clang::VarDecl>((*it)->getDecl());
        if (Var != nullptr) 
          IncVars.insert(Var);
      }

      std::set<clang::VarDecl *> Intersect0;
      std::set_intersection(InitVars.begin(),InitVars.end(),CondVars.begin(),CondVars.end(),
          std::inserter(Intersect0,Intersect0.begin()));

      std::set<clang::VarDecl *> Intersect1;
      std::set_intersection(IncVars.begin(),IncVars.end(),Intersect0.begin(),Intersect0.end(),
          std::inserter(Intersect1,Intersect1.begin()));

      assert(Intersect1.size()==1);
      auto IterVar = *(Intersect1.begin());

      return IterVar;
    }

    void GenerateInitStmt(clang::ForStmt *ForStatement, clang::VarDecl *IterVar) {
      clang::Stmt *InitStmt = ForStatement->getInit();

      CodeGenerator->genForInit(InitStmt, IterVar);
    }

    std::set<clang::VarDecl *> FindKernelArgs(clang::ForStmt *ForStmt) {
      ForVisitor Visitor;

      auto DeclRefExprs = Visitor.getDeclRefExprs(ForStmt);

      std::set<clang::VarDecl *> Temp;
      for (auto it = DeclRefExprs.begin(); it != DeclRefExprs.end(); it++) {
        if (auto Var = llvm::dyn_cast_or_null<clang::VarDecl>((*it)->getDecl())) {
          Temp.insert(Var);
        }
      }

      auto VarDecls = Visitor.getVarDecls(ForStmt);

      std::set<clang::VarDecl *> KernelArgs;
      std::set_difference(Temp.begin(), Temp.end(), VarDecls.begin(), VarDecls.end(),
          std::inserter(KernelArgs, KernelArgs.begin()));

      return KernelArgs;
    }

    void GenerateKernelArgs(clang::ForStmt *ForStatement, clang::VarDecl *IterVar) {
      auto KernelArgs = FindKernelArgs(ForStatement);
      for (auto it = KernelArgs.begin(); it != KernelArgs.end(); it++) {
        if (*it == IterVar) {
          KernelArgs.erase(it);
          break;
        }
      }

      CodeGenerator->genKernelArgs(KernelArgs);
    }

    void GenerateCondStmt(clang::ForStmt *ForStatement, clang::VarDecl *IterVar) {
      clang::Stmt *Cond = ForStatement->getCond();
      clang::Stmt *Body = ForStatement->getBody();

      CodeGenerator->genIf(Cond, Body, nullptr);
    }

    bool VisitForStmt(clang::ForStmt *ForStatement) {
      ForStatement->dump();

      // Find iteration variable
      clang::VarDecl *IterVar = FindIterVar(ForStatement);

      // Generate kernel arguments
      GenerateKernelArgs(ForStatement, IterVar);

      // Generate code for for-loop init statements
      GenerateInitStmt(ForStatement, IterVar);

      // Generate code for for-loop condition
      GenerateCondStmt(ForStatement, IterVar);

      std::cout << CodeGenerator->getCode() << std::endl;

      return true;
    }

    bool VisitDeclRefExpr(clang::DeclRefExpr *DeclRef) {
      return true;
    }

    bool VisitVarDecl(clang::VarDecl *Var) {
      return true;
    }

  private:
    clang::ASTContext &Context;
    std::shared_ptr<CodeGen> CodeGenerator;
};

class FindForClassConsumer: public clang::ASTConsumer {
  public:
    FindForClassConsumer(clang::ASTContext &Context,std::shared_ptr<CodeGen> &CodeGenerator)
      : Visitor(Context,CodeGenerator) {}

    void HandleTranslationUnit(clang::ASTContext &Context) override {
      Visitor.TraverseDecl(Context.getTranslationUnitDecl());
    }

  private:
    FindForClassVisitor Visitor;
};

class FindForClassAction: public clang::ASTFrontendAction {
  public:
    FindForClassAction(std::string Backend_) : Backend(Backend_) {}

    virtual std::unique_ptr<clang::ASTConsumer> CreateASTConsumer(clang::CompilerInstance &Compiler,
                                                                  llvm::StringRef inFile) override {
      std::shared_ptr<CodeGen> CodeGenerator;
      if (Backend.compare("OpenCL") == 0) {
        CodeGenerator = std::shared_ptr<CodeGen>(new OpenCLCodeGen(Compiler.getASTContext()));
      }

      return std::unique_ptr<clang::ASTConsumer>(
          new FindForClassConsumer(Compiler.getASTContext(), CodeGenerator));
    }

  private:
    std::string Backend;
};

// Run a pass to identify CondVar, IncVar and InitVar
// If CondVar == IncVar then start following passes:
//   1. Init pass
//   2. Cond pass
//   3. Body pass

int main(int argc,const char *argv[])
{
  if (argc > 1) {
    clang::tooling::runToolOnCode(std::make_unique<FindForClassAction>("OpenCL"),argv[1]);
  }

  return 0;
}
