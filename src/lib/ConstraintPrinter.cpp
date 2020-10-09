#include "ConstraintPrinter.h"
#include <iostream>

using namespace Constraint;

void ConstraintPrinter::print(std::shared_ptr<Constraint::Constraints> c) {
  os << "// Dictionary\n[\n";
  indentLevel++;
  int num = c->symbols.size();
  for (auto &n : c->symbols) {
    num--;
    os << indent() << n << " : ";
    os << c->symbolType(n) << " = " << c->symbolValue(n);
    std::string ranges = c->symbolRange(n);     // Can be changed if symbolRange returns a pair instead of a string
    int ind = ranges.find(" ");
    std::string low = ranges.substr(0, ind);
    std::string high = ranges.substr(ind+1);

    os << ", range : [" << low <<","<< high<<"]";  // Changed by Rishab

    // Added by Rishab for multiple distributions
    std::string distribution = c->get_distribution(n);
    std::pair<std::string, std::string> params = c->get_params(n);

    if(distribution == "uniform")
      os << ", uniform";

    else if(distribution == "exponential" || distribution == "geometric")
      os << ", " << distribution <<"("<< params.first<<")";

    else
      os << ", " << distribution <<"("<< params.first << "," << params.second <<")";

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

std::string ConstraintPrinter::print(Constraint::Expr* e) {
  e->accept(this); 
  std::string s = visitResults.back();
  visitResults.pop_back();
  return s;
}

void ConstraintPrinter::endVisit(Symbol * element) {
  visitResults.push_back(indent() + element->getName());
}

void ConstraintPrinter::endVisit(IntConstant * element) {
  std::string result = indent() + "(" + element->getConstraint()->type2str(element->getType());
  result += " " + std::to_string(element->getValue()) + ")";
  visitResults.push_back(result);
}

void ConstraintPrinter::endVisit(FloatConstant * element) {
  std::string result = indent() + "(" + element->getConstraint()->type2str(element->getType());
  result += " " + std::to_string(element->getValue()) + ")";
  visitResults.push_back(result);
}

void ConstraintPrinter::endVisit(DoubleConstant * element) {
  std::string result = indent() + "(" + element->getConstraint()->type2str(element->getType());
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
  result += element->getConstraint()->op2str(op) + " ";
  if (op >= Constraint::Expr::Op::FirstCast && op <= Constraint::Expr::Op::LastCast) {
    result += element->getConstraint()->type2str(element->getType());
  }else if(op >= Constraint::Expr::Op::FirstUnaryIntr && op <= Constraint::Expr::Op::LastUnaryIntr)
  {
     result += element->getConstraint()->type2str(element->getType());
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
  auto op = element->getOp();
  result += element->getConstraint()->op2str(op) + " ";

  if(op >= Constraint::Expr::Op::FirstBinaryIntr && op <= Constraint::Expr::Op::LastBinaryIntr)
    result += element->getConstraint()->type2str(element->getType()) + "\n";
  else
    result += "\n";

  result += result1 + "\n";
  result += result2 + "\n";
  result += indent() + ")";
  visitResults.push_back(result);
}

std::string ConstraintPrinter::indent() const {
  return std::string(indentLevel*indentSize, ' ');
}

