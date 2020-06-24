#pragma once 
#include <sstream>
#include <set>
#include <map>
#include <memory>

class ConstraintVisitor;

namespace Constraint {

class Constraint;

/*
 * Representation of types for constraint constants, symbols, and 
 * expressions.
 */
class Type {
public:
  enum Base { Int, Float };

private:
  Base base;
  int width;

public:
  Type(Base b, int w) : base(b), width(w) {}
  ~Type() = default;

  Base getBase() { return base; }
  int getWidth() { return width; }
};

/*
 * This class defines the base of the STG constraint expression hierarchy.
 */
class Expr {
public:
  /* 
   * Operator types represent the operators in the LLVM instruction set
   * and a few additional operators, such as logical connectives.
   */
  enum Op {
    // Used for 0-ary expressions
    None = 0,
    // Unary operators
    Trunc, ZExt, SExt, UItoFP, SItoFP,                // casts from ints
    FPTrunc, FPExt, FPtoUI, FPtoSI,                  // casts from floats
    BitCast,
    LNot,					     // logical not
    FNeg,					     // float negation
    // Binary operators
    Add, Sub, Mul, UDiv, SDiv, URem, SRem,	     // int arithmetic
    And, Or, Xor, Shl, LShr, AShr,	             // bitwise
    Eq, Ne, Ult, Ule, Ugt, Uge, Slt, Sle, Sgt, Sge,  // comparison
    FAdd, FSub, FMul, FDiv, FRem,   		     // float arithmetic
    FOEq, FONe, FOlt, FOle, FOgt, FOge, FOrd, 	     // float comparison
    FUEq, FUNe, FUlt, FUle, FUgt, FUge, FUno, 	     // float comparison
    LAnd, LOr, 					     // logical

    FirstUnary = Trunc, LastUnary = FNeg,
    FirstCast = Trunc, LastCast = BitCast,
    FirstBinary = Add, LastBinary = LOr
  };

protected:
  Op op;
  std::shared_ptr<Type> type;

public:
  virtual ~Expr() = default;

  void setType(std::shared_ptr<Type> t) { type = t; }
  std::shared_ptr<Type> getType() { return type; }
  Op getOp() const { return op; }

  // Delegated visitor hook
  virtual void accept(ConstraintVisitor * visitor) = 0;
};

// Symbol represents a symbolic variable of a given type

class Symbol : public Expr {
private:
  const std::string id;
public:
  Symbol(const std::string &name, std::shared_ptr<Type> t) : id(name)
     { op = Expr::Op::None; type = t; }
  std::string getName() { return id; }
  void accept(ConstraintVisitor * visitor) override;
};

// Constant expressions

class Constant : public Expr { };                                                 

// TBD: consider using a template class for these
class IntConstant : public Constant {
  int v;
public:
  IntConstant(int v, std::shared_ptr<Type> t) : v(v) 
      { type = t; op = Expr::Op::None; }
  int getValue() { return v; }           
  void accept(ConstraintVisitor * visitor) override; 
};

class LongConstant : public Constant {
  long v;
public:
  LongConstant(long v, std::shared_ptr<Type> t) : v(v) 
      { type = t; op = Expr::Op::None; }
  long getValue() { return v; }           
  void accept(ConstraintVisitor * visitor) override; 
};

class FloatConstant : public Constant {
  float v;
public:
  FloatConstant(float v, std::shared_ptr<Type> t) : v(v) 
      { type = t; op = Expr::Op::None; }
  float getValue() { return v; }           
  void accept(ConstraintVisitor * visitor) override; 
};

class DoubleConstant : public Constant {
  double v;
public:
  DoubleConstant(double v, std::shared_ptr<Type> t) : v(v) 
      { type = t; op = Expr::Op::None; }
  double getValue() { return v; }           
  void accept(ConstraintVisitor * visitor) override; 
};

// Unary expressions
class UnaryExpr : public Expr {
  std::shared_ptr<Expr> child[1];
public:
  UnaryExpr(std::shared_ptr<Expr> c, Expr::Op o) { op = o; child[0] = c; }
  UnaryExpr(std::shared_ptr<Expr> c, Expr::Op o, std::shared_ptr<Type> t) 
      { op = o; type = t; child[0] = c; }
  std::shared_ptr<Expr> getChild(int i) { return child[i]; }
  void accept(ConstraintVisitor * visitor) override;
};

// Binary expressions
class BinaryExpr : public Expr {
  std::shared_ptr<Expr> child[2];
public:
  BinaryExpr(std::shared_ptr<Expr> c1, std::shared_ptr<Expr> c2, Expr::Op o)
      { op = o; child[0] = c1; child[1] = c2; }
  std::shared_ptr<Expr> getChild(int i) { return child[i]; }
  void accept(ConstraintVisitor * visitor) override;
};

/*
 * A constraint is a dictionary of symbols and Boolean expression.
 */
class Constraint {
  std::map<std::string, std::string> symbolTypes;
  std::map<std::string, std::string> symbolValues;
  std::shared_ptr<Expr> expr = nullptr;

  // Recording of interned sub-expressions to reduce redundancy
  std::map<Type::Base, std::map<int, std::shared_ptr<Type>>> internType;
  std::map<std::string, std::shared_ptr<Symbol>> internSymbol;
public:
  std::set<std::string> symbols;
  void defineSymbol(std::string n, std::string t, std::string v);
  bool isDefined(std::string n);
  std::string symbolType(std::string n) { return symbolTypes.find(n)->second; }
  std::string symbolValue(std::string n) { return symbolValues.find(n)->second; }

  void setExpr(std::shared_ptr<Expr> e) { expr = e; }
  std::shared_ptr<Expr> getExpr() { return expr; }

  // Create methods for constraint sub-expressions
  std::shared_ptr<Type> create(Type::Base b, int w);

  std::shared_ptr<Symbol> create(std::string name, std::shared_ptr<Type> t);
  std::shared_ptr<IntConstant> create(int v, std::shared_ptr<Type> t);
  std::shared_ptr<LongConstant> create(long v, std::shared_ptr<Type> t);
  std::shared_ptr<FloatConstant> create(float v, std::shared_ptr<Type> t);
  std::shared_ptr<DoubleConstant> create(double v, std::shared_ptr<Type> t);
  std::shared_ptr<UnaryExpr> create(std::shared_ptr<Expr> c, Expr::Op o);
  std::shared_ptr<UnaryExpr> create(std::shared_ptr<Expr> c, Expr::Op o, std::shared_ptr<Type> t);
  std::shared_ptr<BinaryExpr> create(std::shared_ptr<Expr> c1, std::shared_ptr<Expr> c2, Expr::Op o);

  // Translation methods for external and internal representations
  std::shared_ptr<Type> str2type(std::string s);
  std::string type2str(std::shared_ptr<Type> t);
  Expr::Op str2op(std::string s);
  std::string op2str(Expr::Op o);
};

std::optional<std::shared_ptr<Constraint>> parse(std::istream& stream);


}
