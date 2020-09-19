#include <iostream>

#include "llvm/Support/Casting.h" // dyn_cast_or_null
#include "llvm/Support/raw_ostream.h"

#include "clang/AST/PrettyPrinter.h"
#include "clang/AST/Expr.h" // UnaryOperator, etc.

#include "CodeGen.hpp"

/* CodeGen */
CodeGen::CodeGen(clang::ASTContext &Context_, std::string Backend_, std::string EndStmt_) :
  Context(Context_), Backend(Backend_), Code(""), EndStmt(EndStmt_) {}

void CodeGen::clearCode() {
  Code.clear();
}

std::string CodeGen::stmtToString(clang::Stmt *Stmt) {
  std::string str("");

  llvm::raw_string_ostream ostream(str);
  Stmt->printPretty(ostream, nullptr, clang::PrintingPolicy(Context.getLangOpts()));
  ostream.flush();

  str=ostream.str();

  return str;
}

void CodeGen::genCode(clang::Stmt *Stmt) {
  Code.append(stmtToString(Stmt));
}

std::string CodeGen::getCode() {
  return Code;
}

/* OpenCL */
OpenCLCodeGen::OpenCLCodeGen(clang::ASTContext &Context) : CodeGen(Context, "OpenCL", ";\n") {}

void OpenCLCodeGen::genCode(clang::Stmt *Stmt) {
  CodeGen::genCode(Stmt);

  auto Decl = llvm::dyn_cast_or_null<clang::DeclStmt>(Stmt);
  if (Decl == nullptr) {
      Code.append(EndStmt);
  }
}

std::string OpenCLCodeGen::genForInit(clang::Stmt *ForInit, clang::VarDecl *IterVar) {
  //TODO: Buggy when Iter var is not declared in ForInit
  genCode(ForInit);
  std::string VarName = IterVar->getNameAsString();
  Code.append(VarName + " = " + VarName + " + " + "get_global_id(0)" + EndStmt);
  return Code;
}

std::string OpenCLCodeGen::genKernelArgs(std::set<clang::VarDecl *> &s) {
  Code.append("__kernel void knl(");

  for (auto it = s.begin(); it != s.end(); it++) {
    auto QualType = (*it)->getType();
    if (QualType->isPointerType()) {
      Code.append("__global ");
    }
    Code.append(QualType.getAsString() + " " + (*it)->getNameAsString());

    if (it != std::prev(s.end())) {
      Code.append(", ");
    }
  }
  Code.append(") {\n");

  return Code;
}

std::string OpenCLCodeGen::genIf(clang::Stmt *Cond, clang::Stmt *Then, clang::Stmt *Else) {
  assert(Cond != nullptr);
  assert(Then != nullptr);

  Code.append("if (" + CodeGen::stmtToString(Cond) + ") ");
  if (auto Compound = llvm::dyn_cast_or_null<clang::CompoundStmt>(Then)) {
    Code.append(CodeGen::stmtToString(Then));
  } else {
    Code.append(" {\n" + CodeGen::stmtToString(Then) + "\n}");
  }

  if (Else != nullptr) {
    Code.append(" else ");
    if (auto Compound = llvm::dyn_cast_or_null<clang::CompoundStmt>(Else)) {
      Code.append(CodeGen::stmtToString(Else));
    } else {
      Code.append(" {\n" + CodeGen::stmtToString(Else) + "\n}");
    }
  }

  Code.append("\n");

  return Code;
}
