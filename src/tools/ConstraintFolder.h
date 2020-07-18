#pragma once

#include "ConstraintVisitor.h"
#include "ConstraintPrinter.h"

#include <string>
#include <vector>
#include <optional>

class ConstraintFolder: public ConstraintVisitor {
public:
  ConstraintFolder() {}

  void fold(std::shared_ptr<Constraint::Constraints> constraint, bool verbose);

  /* 
   * This visitor visits the entire expression, customizing the  
   * processing at the end of each sub-expression.
   */
  void endVisit(Symbol * element) override;
  void endVisit(IntConstant * element) override;
  void endVisit(DoubleConstant * element) override;
  void endVisit(FloatConstant * element) override;
  void endVisit(UnaryExpr * element) override;
  void endVisit(BinaryExpr * element) override;

private:
  bool verbose = false;

  void createBooleanConstant(bool b);

  ConstraintPrinter cp;
  Constraint::Constraints* constraint;

  // vector holds a new expression to be spliced in or std::nullopt
  std::vector<std::optional<std::shared_ptr<Expr>>> visitResults;
};
