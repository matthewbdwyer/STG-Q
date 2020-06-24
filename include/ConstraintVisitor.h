#pragma once

#include "Constraint.h"

using namespace Constraint;

/*
 * Constraint visitors process expressions within a Constraint.
 * Each sub-expression is visited based on the value returned by "visit()"
 * and post-visit processing of a sub-expression is performed by "endVisit()"
 * calls.
 */
class ConstraintVisitor {
public:

  virtual bool visit(Symbol * element)  { return true; }
  virtual void endVisit(Symbol * element) {}
  virtual bool visit(IntConstant * element) { return true; }
  virtual void endVisit(IntConstant * element) {}
  virtual bool visit(LongConstant * element) { return true; }
  virtual void endVisit(LongConstant * element) {}
  virtual bool visit(FloatConstant * element) { return true; }
  virtual void endVisit(FloatConstant * element) {}
  virtual bool visit(DoubleConstant * element) { return true; }
  virtual void endVisit(DoubleConstant * element) {}
  virtual bool visit(UnaryExpr * element) { return true; }
  virtual void endVisit(UnaryExpr * element) {}
  virtual bool visit(BinaryExpr * element) { return true; }
  virtual void endVisit(BinaryExpr * element) {}

};
