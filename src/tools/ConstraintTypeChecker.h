#pragma once

#include <string>
#include <vector>

#include "ConstraintVisitor.h"

class ConstraintTypeChecker: public ConstraintVisitor {
public:
  ConstraintTypeChecker() {}

  bool check(std::shared_ptr<Constraint::Constraint> constraint, bool verbose);

  /* 
   * This visitor visits the entire expression, customizing the  
   * processing at the end of each sub-expression.
   */
  void endVisit(Symbol * element) override;
  void endVisit(IntConstant * element) override;
  void endVisit(LongConstant * element) override;
  void endVisit(DoubleConstant * element) override;
  void endVisit(FloatConstant * element) override;
  void endVisit(UnaryExpr * element) override;
  void endVisit(BinaryExpr * element) override;

private:
  // Type checking result for constraint
  bool result = true;

  bool verbose = false;

  /* 
   * Records the strings produced by visiting sub-expressions.
   * There are at most two, since expressions are at most binary.
   * Keep track of current child with index.
   */
  std::vector<std::shared_ptr<Constraint::Type>> visitResults;
};
