#include "ConstraintTypeChecker.h"

#include <iostream>
#include <cassert>

using namespace Constraint;
using namespace std;

bool ConstraintTypeChecker::check(std::shared_ptr<Constraint::Constraints> c, bool v) {
  // Enable verbose mode for type checker
  verbose = v;
  
  c->getExpr()->accept(this); 

  // Top level expression must be Boolean
  auto t = visitResults.back();
  visitResults.pop_back();

  if (result) {
    if (!(t->getBase() == Type::Base::Int && t->getWidth() == 1)) {
      cerr << "Type Error: Expected Boolean Constraint\n";
      result = false;
    }
  }

  return result;
}

void ConstraintTypeChecker::endVisit(Symbol * element) {
  visitResults.push_back(element->getType());
  if (verbose)
    cerr << "Type Checker : symbol of type "+element->getConstraint()->type2str(element->getType())+"\n";
}

void ConstraintTypeChecker::endVisit(IntConstant * element) {
  visitResults.push_back(element->getType());
  if (verbose)
    cerr << "Type Checker : constant of type "+element->getConstraint()->type2str(element->getType())+"\n";
}

void ConstraintTypeChecker::endVisit(FloatConstant * element) {
  visitResults.push_back(element->getType());
  if (verbose)
    cerr << "Type Checker : constant of type "+element->getConstraint()->type2str(element->getType())+"\n";
}

void ConstraintTypeChecker::endVisit(DoubleConstant * element) {
  visitResults.push_back(element->getType());
  if (verbose)
    cerr << "Type Checker : constant of type "+element->getConstraint()->type2str(element->getType())+"\n";
}

/*
 * If the type constraints are satisfied the type of the binary
 * expression is set, but not in the case of Cast instructions
 * since they had their types set at creation time (since it is
 * explicit in the constraint syntax).
 */
void ConstraintTypeChecker::endVisit(UnaryExpr * element) {
  if (!result) return;

  auto result1 = visitResults.back();
  visitResults.pop_back();

  auto op = element->getOp();

  auto constraint = element->getConstraint();

  if (Expr::Op::Trunc <= op && op <= Expr::Op::SItoFP) {
    if (!(result1->getBase() == Type::Base::Int)) {
      cerr << "Type Error: Operator "+constraint->op2str(op);
      cerr << " has operand of type "+constraint->type2str(result1);
      cerr << "\n";
      result = false;
    }
  } else if (Expr::Op::FPTrunc <= op && op <= Expr::Op::FPtoSI) {
    if (!(result1->getBase() == Type::Base::Float)) {
      cerr << "Type Error: Operator "+constraint->op2str(op);
      cerr << " has operand of type "+constraint->type2str(result1);
      cerr << "\n";
      result = false;
    }
  } else if (Expr::Op::BitCast == op) {
    if (result1->getWidth() != element->getType()->getWidth()) {
      cerr << "Type Error: Operator "+constraint->op2str(op);
      cerr << " expected width "+element->getType()->getWidth();
      cerr << " but operand has width "+result1->getWidth();
      cerr << "\n";
      result = false;
    }
  } else if (op == Expr::Op::LNot) {
    if (!(result1->getBase() == Type::Base::Int && 
          result1->getWidth() == 1)) {
      cerr << "Type Error: Operator "+constraint->op2str(op);
      cerr << " has operand of type "+constraint->type2str(result1);
      cerr << "\n";
      result = false;
    }
    element->setType(result1);
  } else if (op == Expr::Op::FNeg) {
    if (!(result1->getBase() == Type::Base::Float)) {
      cerr << "Type Error: Operator "+constraint->op2str(op);
      cerr << " has operand of type "+constraint->type2str(result1);
      cerr << "\n";
      result = false;
    }
    element->setType(result1);
  }

  else if(Expr::Op::Sinf32 <= op && op <= Expr::Op::Sqrt){ //Added by Rishab for Unary Intrinsics   Ceilppcf128)
    // std::string operator_string = constraint->op2str(op);
    // std::cout<< "operator string: "<< operator_string <<"\n";
    // int operator_width = stoi(operator_string.substr(operator_string.length()-2));

    // if(operator_width == 28)
    //   operator_width = 128;

    // (Sin double x)

     // std::cout<<"Comming here: sinf32  ->  "<<constraint->type2str(element->getType())<<"\n";

    if (!(result1->getBase() == Type::Base::Float)) {    //  && result1->getWidth() == operator_width 
      cerr << "Type Error: Operator "+constraint->op2str(op);
      cerr << " has operand of type "+constraint->type2str(result1);
      cerr << "\n";
      result = false;
    }
    // element->setType(constraint->str2type(constraint->type2str(element->getType())));
    element->setType(element->getType());
  }

  else {
    cerr << "Type Error: invalid UnaryExpr operator "+constraint->op2str(op)+"\n";
    assert(false);
  }

  visitResults.push_back(element->getType());

  if (verbose) {
    cerr << "Type Checker : operator "+constraint->op2str(op);
    cerr << " of type "+constraint->type2str(element->getType())+"\n";
  }
}   	

/*
 * If the type constraints are satisfied the type of the binary
 * expression is set.
 */
void ConstraintTypeChecker::endVisit(BinaryExpr * element) {
  if (!result) return;

  auto result2 = visitResults.back();
  visitResults.pop_back();
  auto result1 = visitResults.back();
  visitResults.pop_back();

  auto op = element->getOp();

  auto constraint = element->getConstraint();

  if (Expr::Op::Add <= op && op <= Expr::Op::AShr) {
    if (!(result1->getBase() == Type::Base::Int && 
          result2->getBase() == Type::Base::Int &&
          result1->getWidth() == result2->getWidth())) {
      cerr << "Type Error: Operator "+constraint->op2str(op);
      cerr << " has operands of type "+constraint->type2str(result1);
      cerr << " and "+constraint->type2str(result2);
      cerr << "\n";
      result = false;
    }
    element->setType(result1);
  } else if (Expr::Op::Eq <= op && op <= Expr::Op::Sge) {
    if (!(result1->getBase() == Type::Base::Int && 
          result2->getBase() == Type::Base::Int &&
          result1->getWidth() == result2->getWidth())) {
      cerr << "Type Error: Operator "+constraint->op2str(op);
      cerr << " has operands of type "+constraint->type2str(result1);
      cerr << " and "+constraint->type2str(result2);
      cerr << "\n";
      result = false;
    }
    element->setType(constraint->str2type("i1"));
  } else if (Expr::Op::FAdd <= op && op <= Expr::Op::FRem) {
    if (!(result1->getBase() == Type::Base::Float && 
          result2->getBase() == Type::Base::Float &&
          result1->getWidth() == result2->getWidth())) {
      cerr << "Type Error: Operator "+constraint->op2str(op);
      cerr << " has operands of type "+constraint->type2str(result1);
      cerr << " and "+constraint->type2str(result2);
      cerr << "\n";
      result = false;
    }
    element->setType(result1);
  } else if (Expr::Op::FOEq <= op && op <= Expr::Op::FUno) {
    if (!(result1->getBase() == Type::Base::Float && 
          result2->getBase() == Type::Base::Float &&
          result1->getWidth() == result2->getWidth())) {
      cerr << "Type Error: Operator "+constraint->op2str(op);
      cerr << " has operands of type "+constraint->type2str(result1);
      cerr << " and "+constraint->type2str(result2);
      cerr << "\n";
      result = false;
    }
    element->setType(constraint->str2type("i1"));
  } else if (Expr::Op::LAnd <= op && op <= Expr::Op::LOr) {
    if (!(result1->getBase() == Type::Base::Int && 
          result2->getBase() == Type::Base::Int &&
          result1->getWidth() == 1 && result2->getWidth() == 1)) { 
      cerr << "Type Error: Operator "+constraint->op2str(op);
      cerr << " has operands of type "+constraint->type2str(result1);
      cerr << " and "+constraint->type2str(result2);
      cerr << "\n";
      result = false;
    }
    element->setType(result1);
  }
  else if(Expr::Op::Powf32 <= op && op <= Expr::Op::Pow){  //Added by Rishab for Binary Intrinsics    Copysignppcf128
    // std::string operator_string = constraint->op2str(op);
    // int operator_width = stoi(operator_string.substr(operator_string.length()-2));

    // if(operator_width == 28)
    //   operator_width = 128;

    if (!(result1->getBase() == Type::Base::Float && 
          result2->getBase() == Type::Base::Float &&
          result1->getWidth() == result2->getWidth())) {  // result1->getWidth() == operator_width && result2->getWidth() == operator_width
      cerr << "Type Error: Operator "+constraint->op2str(op);
      cerr << " has operands of type "+constraint->type2str(result1);
      cerr << " and "+constraint->type2str(result2);
      cerr << "\n";
      result = false;
    }
    element->setType(result1);
  }
  else {
    cerr << "Type Error: invalid BinaryExpr operator "+constraint->op2str(op)+"\n";
    assert(false);
  }

  visitResults.push_back(element->getType());

  if (verbose) {
    cerr << "Type Checker : operator "+constraint->op2str(op);
    cerr << " of type "+constraint->type2str(element->getType())+"\n";
  }

}
