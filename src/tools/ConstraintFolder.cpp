#include "ConstraintFolder.h"

#include <iostream>
#include <optional>
#include <cassert>

#include <math.h>

using namespace Constraint;
using namespace std;

void ConstraintFolder::fold(std::shared_ptr<Constraint::Constraints> c, bool v) {
  // Enable verbose mode for folder
  verbose = v;
  constraint = c.get();
  
  c->getExpr()->accept(this); 

  if (auto maybeNewExpr = visitResults.back(); maybeNewExpr) {
     c->setExpr(maybeNewExpr.value());
  }
  visitResults.pop_back();
}

void ConstraintFolder::endVisit(Symbol * element) {
  visitResults.push_back(std::nullopt);
}

void ConstraintFolder::endVisit(IntConstant * element) {
  visitResults.push_back(std::nullopt);
}

void ConstraintFolder::endVisit(FloatConstant * element) {
  visitResults.push_back(std::nullopt);
}

void ConstraintFolder::endVisit(DoubleConstant * element) {
  visitResults.push_back(std::nullopt);
}

template<typename T>
long convertInRange(long v, std::string tn) {
  if (v > std::numeric_limits<T>::max() ||
      v < std::numeric_limits<T>::min()) {
    cerr << "Folder : conversion to integer exceeds capacity of "+tn+"\n";
    assert(false);
  }
  return (T)(v);
}

long truncInt(long v, Type* t) {
  assert(t->getBase() == Type::Base::Int);
  switch (t->getWidth()) {
    case 1: return (v % 2 == 0) ? 0 : 1; 
    case 8: return convertInRange<int8_t>(v,"i8");
    case 16: return convertInRange<int16_t>(v,"i16");
    case 32: return convertInRange<int32_t>(v,"i32");
    case 64: return convertInRange<int64_t>(v,"i64");
    default: assert(false);
  }
}

/* 
 * If operand is constant, then evaluate operator and replace it
 * with a new constant expression.
 */
void ConstraintFolder::endVisit(UnaryExpr * element) {
  // If there is a new folded child splice it into this node
  if (auto maybeNewChild = visitResults.back(); maybeNewChild) {
     element->setChild(0, maybeNewChild.value());
  }
  visitResults.pop_back();

  auto child = element->getChild(0);
  if (auto c = dynamic_pointer_cast<Constant>(child)) {
    auto op = element->getOp();

    if (verbose) {
      cerr << "Folder :\n"+cp.print(element)+"\n";
    }

    if (Expr::Op::Trunc <= op && op <= Expr::Op::SItoFP) {
      // Integer casts
      switch(op) {
        case Expr::Op::Trunc:
          {
            auto ci = dynamic_pointer_cast<IntConstant>(child);
            ci->setValue(truncInt(ci->getValue(), element->getType().get()));
            ci->setType(element->getType());
            visitResults.push_back(std::optional<std::shared_ptr<Expr>>(child));
          }
          break;

        case Expr::Op::ZExt:
          {
            auto ci = dynamic_pointer_cast<IntConstant>(child);
            ci->setType(element->getType());
            visitResults.push_back(std::optional<std::shared_ptr<Expr>>(child));
          }
          break;

        case Expr::Op::SItoFP:
          {
            auto ci = dynamic_pointer_cast<IntConstant>(child);
            if (element->getType()->getWidth() == 32) {
              float fv = (float)ci->getValue(); 
              auto fc = constraint->create(fv, constraint->str2type("float"));
              visitResults.push_back(std::optional<std::shared_ptr<Expr>>(fc));
            } else {
              double dv = (float)ci->getValue(); 
              auto dc = constraint->create(dv, constraint->str2type("double"));
              visitResults.push_back(std::optional<std::shared_ptr<Expr>>(dc));
            } 
          }
          break;

        case Expr::Op::SExt:
        case Expr::Op::UItoFP:
          visitResults.push_back(std::nullopt);
      }

    } else if (Expr::Op::FPTrunc <= op && op <= Expr::Op::FPtoSI) {
      // Float casts
      switch(op) {
        case Expr::Op::FPTrunc:
          {
            // Can only truncate downward from double to float
            if (auto di = dynamic_pointer_cast<DoubleConstant>(child)) {
              float fv = (float)di->getValue(); 
              auto fc = constraint->create(fv, constraint->str2type("float"));
              visitResults.push_back(std::optional<std::shared_ptr<Expr>>(fc));
            } else {
              cerr << "Folder : expected double but found "+cp.print(child.get())+"\n";
              visitResults.push_back(std::nullopt);
            }
          }
          break;
        case Expr::Op::FPExt:
          {
            // Can only extend upward from float to double
            auto fi = dynamic_pointer_cast<FloatConstant>(child);
            double dv = (double)fi->getValue(); 
            auto dc = constraint->create(dv, constraint->str2type("double"));
            visitResults.push_back(std::optional<std::shared_ptr<Expr>>(dc));
          }
          break;
          
        case Expr::Op::FPtoSI:
          {
            long lv = 0;
            if (auto fi = dynamic_pointer_cast<FloatConstant>(child)) {
              lv = (long)fi->getValue();
            } else {
              auto di = dynamic_pointer_cast<DoubleConstant>(child);
              lv = (long)di->getValue();
            } 
            auto ic = constraint->create(truncInt(lv, element->getType().get()), element->getType());
            visitResults.push_back(std::optional<std::shared_ptr<Expr>>(ic));
          } 
          break;
        case Expr::Op::FPtoUI:
          visitResults.push_back(std::nullopt);
      }

    } else if (op == Expr::Op::LNot) {
      auto ci = dynamic_pointer_cast<IntConstant>(child);
      ci->setValue(1 - ci->getValue()); 
      visitResults.push_back(std::optional<std::shared_ptr<Expr>>(child));

    } else if (op == Expr::Op::FNeg) {
      if (auto fi = dynamic_pointer_cast<FloatConstant>(child)) {
        fi->setValue(-1.0 * fi->getValue()); 
      } else {
        auto di = dynamic_pointer_cast<DoubleConstant>(child);
        di->setValue(-1.0 * di->getValue()); 
      } 
      visitResults.push_back(std::optional<std::shared_ptr<Expr>>(child));

    } else {
      // The BitCast operator is not supported
      visitResults.push_back(std::nullopt);
    } 

    if (verbose) {
      if (auto maybeReplacement = visitResults.back(); maybeReplacement) {
         cerr << "replaced with\n"+cp.print(maybeReplacement.value().get())+"\n";
      } else {
         cerr << "retained\n";
      }
    }

  } else {
    // Operand is not constant
    visitResults.push_back(std::nullopt);
  }

}   		

void ConstraintFolder::createBooleanConstant(bool b) {
  long bv = (b) ? 1 : 0; 
  auto bc = constraint->create(bv, constraint->str2type("i1"));
  visitResults.push_back(std::optional<std::shared_ptr<Expr>>(bc));
}

/*
 * Fold constants for binary operators.
 * TBD: check for over/underflow based on type
 */
void ConstraintFolder::endVisit(BinaryExpr * element) {
  /* 
   * If there are new folded children splice them into this node.
   * visitResults managed as a stack, so second child comes first.
   */
  if (auto maybeNewChild1 = visitResults.back(); maybeNewChild1) {
     element->setChild(1, maybeNewChild1.value());
  }
  visitResults.pop_back();

  if (auto maybeNewChild0 = visitResults.back(); maybeNewChild0) {
     element->setChild(0, maybeNewChild0.value());
  }
  visitResults.pop_back();

  auto child0 = element->getChild(0);
  auto child1 = element->getChild(1);
  if (auto c0 = dynamic_pointer_cast<Constant>(child0)) {
    if (auto c1 = dynamic_pointer_cast<Constant>(child1)) {
      auto op = element->getOp();

      if (verbose) {
        cerr << "Folder :\n"+cp.print(element)+"\n";
      }

      if ((Expr::Op::Add <= op && op <= Expr::Op::Sge) || (op == Expr::Op::LAnd) || (op == Expr::Op::LOr)) {
        // Integer operands
        auto ic0 = dynamic_pointer_cast<IntConstant>(child0);
        auto ic1 = dynamic_pointer_cast<IntConstant>(child1);
        auto v0 = ic0->getValue();
        auto v1 = ic1->getValue();
        auto t0 = ic0->getType().get();

        switch(op) {
          case Expr::Op::Add:
            ic0->setValue(truncInt(v0+v1, t0));
            visitResults.push_back(std::optional<std::shared_ptr<Expr>>(child0));
            break;

          case Expr::Op::Sub:
            ic0->setValue(truncInt(v0-v1, t0));
            visitResults.push_back(std::optional<std::shared_ptr<Expr>>(child0));
            break;

          case Expr::Op::Mul:
            ic0->setValue(truncInt(v0*v1, t0));
            visitResults.push_back(std::optional<std::shared_ptr<Expr>>(child0));
            break;

          case Expr::Op::SDiv:
            ic0->setValue(truncInt(v0/v1, t0));
            visitResults.push_back(std::optional<std::shared_ptr<Expr>>(child0));
            break;

          case Expr::Op::SRem:
            ic0->setValue(truncInt(v0%v1, t0));
            visitResults.push_back(std::optional<std::shared_ptr<Expr>>(child0));
            break;

          case Expr::Op::Eq:
            createBooleanConstant(v0 == v1);
            break;

          case Expr::Op::Ne:
            createBooleanConstant(v0 != v1);
            break;

          case Expr::Op::Slt:
            createBooleanConstant(v0 < v1);
            break;

          case Expr::Op::Sle:
            createBooleanConstant(v0 <= v1);
            break;

          case Expr::Op::Sgt:
            createBooleanConstant(v0 > v1);
            break;

          case Expr::Op::Sge:
            createBooleanConstant(v0 >= v1);
            break;

          case Expr::Op::LAnd:
            ic0->setValue(std::min(v0,v1)); 
            visitResults.push_back(std::optional<std::shared_ptr<Expr>>(child0));
            break;

          case Expr::Op::LOr:
            ic0->setValue(std::max(v0,v1)); 
            visitResults.push_back(std::optional<std::shared_ptr<Expr>>(child0));
            break;

          // These bitwise and unsigned operators are not supported (yet)
          case Expr::Op::And:
          case Expr::Op::Or:
          case Expr::Op::Xor:
          case Expr::Op::Shl:
          case Expr::Op::AShr:
          case Expr::Op::LShr:
          case Expr::Op::UDiv:
          case Expr::Op::URem:
          case Expr::Op::Ult:
          case Expr::Op::Ule:
          case Expr::Op::Ugt:
          case Expr::Op::Uge:
            visitResults.push_back(std::nullopt);
            break;
        }

      } else if (Expr::Op::FAdd <= op && op <= Expr::Op::FUno) {
        // Float or double operators
        if (auto fc0 = dynamic_pointer_cast<FloatConstant>(child0)) {
          auto fc1 = dynamic_pointer_cast<FloatConstant>(child1);
          auto v0 = fc0->getValue();
          auto v1 = fc1->getValue();
          auto qnan = std::numeric_limits<float>::quiet_NaN();

          switch(op) {
            case Expr::Op::FAdd:
              fc0->setValue(v0+v1);
              visitResults.push_back(std::optional<std::shared_ptr<Expr>>(child0));
              break;
            case Expr::Op::FSub:
              fc0->setValue(v0-v1);
              visitResults.push_back(std::optional<std::shared_ptr<Expr>>(child0));
              break;
            case Expr::Op::FMul:
              fc0->setValue(v0*v1);
              visitResults.push_back(std::optional<std::shared_ptr<Expr>>(child0));
              break;
            case Expr::Op::FDiv:
              fc0->setValue(v0/v1);
              visitResults.push_back(std::optional<std::shared_ptr<Expr>>(child0));
              break;
            case Expr::Op::FRem:
              fc0->setValue(fmod(v0,v1));
              visitResults.push_back(std::optional<std::shared_ptr<Expr>>(child0));
              break;
            case Expr::Op::FOEq:
              createBooleanConstant(v0 != qnan && v1 != qnan && v0 == v1);
              break;
            case Expr::Op::FONe:
              createBooleanConstant(v0 != qnan && v1 != qnan && v0 != v1);
              break;
            case Expr::Op::FOlt:
              createBooleanConstant(v0 != qnan && v1 != qnan && v0 < v1);
              break;
            case Expr::Op::FOle:
              createBooleanConstant(v0 != qnan && v1 != qnan && v0 <= v1);
              break;
            case Expr::Op::FOgt:
              createBooleanConstant(v0 != qnan && v1 != qnan && v0 > v1);
              break;
            case Expr::Op::FOge:
              createBooleanConstant(v0 != qnan && v1 != qnan && v0 >= v1);
              break;
            case Expr::Op::FOrd:
              createBooleanConstant(v0 != qnan && v1 != qnan);
              break;
            case Expr::Op::FUEq:
              createBooleanConstant(v0 == qnan || v1 == qnan || v0 == v1);
              break;
            case Expr::Op::FUNe:
              createBooleanConstant(v0 == qnan || v1 == qnan || v0 != v1);
              break;
            case Expr::Op::FUlt:
              createBooleanConstant(v0 == qnan || v1 == qnan || v0 < v1);
              break;
            case Expr::Op::FUle:
              createBooleanConstant(v0 == qnan || v1 == qnan || v0 <= v1);
              break;
            case Expr::Op::FUgt:
              createBooleanConstant(v0 == qnan || v1 == qnan || v0 > v1);
              break;
            case Expr::Op::FUge:
              createBooleanConstant(v0 == qnan || v1 == qnan || v0 >= v1);
              break;
            case Expr::Op::FUno:
              createBooleanConstant(v0 == qnan || v1 == qnan);
              break;
          }

        } else {
          auto dc0 = dynamic_pointer_cast<DoubleConstant>(child0);
          auto dc1 = dynamic_pointer_cast<DoubleConstant>(child1);
          auto v0 = dc0->getValue();
          auto v1 = dc1->getValue();
          auto qnan = std::numeric_limits<double>::quiet_NaN();

          switch(op) {
            case Expr::Op::FAdd:
              dc0->setValue(v0+v1);
              visitResults.push_back(std::optional<std::shared_ptr<Expr>>(child0));
              break;
            case Expr::Op::FSub:
              dc0->setValue(v0-v1);
              visitResults.push_back(std::optional<std::shared_ptr<Expr>>(child0));
              break;
            case Expr::Op::FMul:
              dc0->setValue(v0*v1);
              visitResults.push_back(std::optional<std::shared_ptr<Expr>>(child0));
              break;
            case Expr::Op::FDiv:
              dc0->setValue(v0/v1);
              visitResults.push_back(std::optional<std::shared_ptr<Expr>>(child0));
              break;
            case Expr::Op::FRem:
              dc0->setValue(fmod(v0,v1));
              visitResults.push_back(std::optional<std::shared_ptr<Expr>>(child0));
              break;
            case Expr::Op::FOEq:
              createBooleanConstant(v0 != qnan && v1 != qnan && v0 == v1);
              break;
            case Expr::Op::FONe:
              createBooleanConstant(v0 != qnan && v1 != qnan && v0 != v1);
              break;
            case Expr::Op::FOlt:
              createBooleanConstant(v0 != qnan && v1 != qnan && v0 < v1);
              break;
            case Expr::Op::FOle:
              createBooleanConstant(v0 != qnan && v1 != qnan && v0 <= v1);
              break;
            case Expr::Op::FOgt:
              createBooleanConstant(v0 != qnan && v1 != qnan && v0 > v1);
              break;
            case Expr::Op::FOge:
              createBooleanConstant(v0 != qnan && v1 != qnan && v0 >= v1);
              break;
            case Expr::Op::FOrd:
              createBooleanConstant(v0 != qnan && v1 != qnan);
              break;
            case Expr::Op::FUEq:
              createBooleanConstant(v0 == qnan || v1 == qnan || v0 == v1);
              break;
            case Expr::Op::FUNe:
              createBooleanConstant(v0 == qnan || v1 == qnan || v0 != v1);
              break;
            case Expr::Op::FUlt:
              createBooleanConstant(v0 == qnan || v1 == qnan || v0 < v1);
              break;
            case Expr::Op::FUle:
              createBooleanConstant(v0 == qnan || v1 == qnan || v0 <= v1);
              break;
            case Expr::Op::FUgt:
              createBooleanConstant(v0 == qnan || v1 == qnan || v0 > v1);
              break;
            case Expr::Op::FUge:
              createBooleanConstant(v0 == qnan || v1 == qnan || v0 >= v1);
              break;
            case Expr::Op::FUno:
              createBooleanConstant(v0 == qnan || v1 == qnan);
              break;
          }

        }

      } else {
        // Catch any other operators
        cerr << "Folder : unexpected binary operator "+constraint->op2str(op)+"\n";
        assert(false);
      }


      if (verbose) {
        if (auto maybeReplacement = visitResults.back(); maybeReplacement) {
           cerr << "replaced with\n"+cp.print(maybeReplacement.value().get())+"\n";
        } else {
           cerr << "retained\n";
        }
      }

    } else {
      // child1 is not constant
      visitResults.push_back(std::nullopt);
    }

  } else {
    // child0 is not constant
    visitResults.push_back(std::nullopt);
  }


}
