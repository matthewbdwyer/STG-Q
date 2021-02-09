#pragma once

#include "ConstraintVisitor.h"
#include <ostream>
#include <iostream>
#include <string>
#include <vector>
#include <fstream>

class BVPrinter: public ConstraintVisitor {
public:
  BVPrinter() : os(std::cout), indentSize(2) {}
  BVPrinter(std::ostream &os, int indentSize ) : 
      os(os), indentSize(indentSize) {}

  void print(std::shared_ptr<Constraint::Constraints> constraint, const char *dict);

  void parseDict(const char *dict, std::shared_ptr<Constraint::Constraints> constraint, std::string var);

  /* 
   * This visitor visits the entire expression, customizing the  
   * processing at the end of each sub-expression.
   */
  void endVisit(Symbol * element) override;
  void endVisit(IntConstant * element) override;
  void endVisit(DoubleConstant * element) override;
  void endVisit(FloatConstant * element) override;
  bool visit(UnaryExpr * element) override;
  void endVisit(UnaryExpr * element) override;
  bool visit(BinaryExpr * element) override;
  void endVisit(BinaryExpr * element) override;

private:
  std::string indent() const;
  int indentLevel = 0;
  int indentSize = 2;

  std::ostream &os;
  std::shared_ptr<Constraint::Constraints> theConstraint;

  /* 
   * Records the strings produced by visiting sub-expressions.
   * There are at most two, since expressions are at most binary.
   * Keep track of current child with index.
   */
  std::vector<std::string> visitResults;
};
