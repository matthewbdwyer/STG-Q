#include "ConstraintPrinter.h"
#include <iostream>

using namespace Constraint;

void ConstraintPrinter::print(std::shared_ptr<Constraint::Constraint> c) {
  theConstraint = c;
  os << "// Dictionary\n[\n";
  indentLevel++;
  int num = c->symbols.size();
  for (auto &n : c->symbols) {
    num--;
    os << indent() << n << " : ";
    os << c->symbolType(n) << " = " << c->symbolValue(n);
    os << ((num>0) ? ",\n" : "\n");
  }
  indentLevel--;
  os << "]\n";

  os << "// Constraint\n";
  c->getExpr()->accept(this); 
  os << visitResults.back();
  visitResults.pop_back();
  os << "\n";

  os.flush();
}

void ConstraintPrinter::endVisit(Symbol * element) {
  visitResults.push_back(indent() + element->getName());
}

void ConstraintPrinter::endVisit(IntConstant * element) {
  std::string result = indent() + "(" + theConstraint->type2str(element->getType());
  result += " " + std::to_string(element->getValue()) + ")";
  visitResults.push_back(result);
}

void ConstraintPrinter::endVisit(LongConstant * element) {
  std::string result = indent() + "(" + theConstraint->type2str(element->getType());
  result += " " + std::to_string(element->getValue()) + ")";
  visitResults.push_back(result);
}

void ConstraintPrinter::endVisit(FloatConstant * element) {
  std::string result = indent() + "(" + theConstraint->type2str(element->getType());
  result += " " + std::to_string(element->getValue()) + ")";
  visitResults.push_back(result);
}

void ConstraintPrinter::endVisit(DoubleConstant * element) {
  std::string result = indent() + "(" + theConstraint->type2str(element->getType());
  result += " " + std::to_string(element->getValue()) + ")";
  visitResults.push_back(result);
}

bool ConstraintPrinter::visit(UnaryExpr * element) {
  indentLevel++;
  return true;
}

void ConstraintPrinter::endVisit(UnaryExpr * element) {
  std::string result1 = visitResults.back();
  visitResults.pop_back();

  auto op = element->getOp();

  indentLevel--;
  std::string result = indent() + "(";
  result += theConstraint->op2str(op) + " ";
  if (op >= Constraint::Expr::Op::FirstCast && op <= Constraint::Expr::Op::LastCast) {
    result += theConstraint->type2str(element->getType());
  }
  result += "\n";
  result += result1 + "\n";
  result += indent() + ")";
  visitResults.push_back(result);
}   		

bool ConstraintPrinter::visit(BinaryExpr * element) {
  indentLevel++;
  return true;
}

void ConstraintPrinter::endVisit(BinaryExpr * element) {
  std::string result2 = visitResults.back();
  visitResults.pop_back();
  std::string result1 = visitResults.back();
  visitResults.pop_back();

  indentLevel--;
  std::string result = indent() + "(";
  result += theConstraint->op2str(element->getOp()) + "\n";
  result += result1 + "\n";
  result += result2 + "\n";
  result += indent() + ")";
  visitResults.push_back(result);
}   									\

std::string ConstraintPrinter::indent() const {
  return std::string(indentLevel*indentSize, ' ');
}

