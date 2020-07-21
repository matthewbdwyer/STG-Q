#pragma once 
#include <sstream>
#include <set>
#include <map>
#include <memory>

class ConstraintVisitor;

namespace Constraint {

class Constraints;

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

   //added by SBH for unary llvm intrinsics

   Sinf32, Sinf64, Sinf80, Sinf128, Sinppcf128,
   Cosf32, Cosf64, Cosf80, Cosf128, Cosppcf128,
   Expf32, Expf64, Expf80, Expf128, Expppcf128,
   Exp2f32, Exp2f64, Exp2f80, Exp2f128, Exp2ppcf128,
   Logf32, Logf64, Logf80, Logf128, Logppcf128,

   Log2f32, Log2f64, Log2f80, Log2f128, Log2ppcf128,

   Log10f32, Log10f64, Log10f80, Log10f128, Log10ppcf128,

   Fabsf32, Fabsf64, Fabsf80, Fabsf128, Fabsppcf128,


   Sqrtf32, Sqrtf64, Sqrtf80, Sqrtf128, Sqrtppcf128,
   Floorf32, Floorf64, Floorf80, Floorf128, Floorppcf128,
   Ceilf32, Ceilf64, Ceilf80, Ceilf128, Ceilppcf128,

  //added by SBH for binary llvm intrinsics


   Powf32, Powf64, Powf80, Powf128, Powppcf128,
   Powif32, Powif64, Powif80, Powif128, Powippcf128,
   Fmaf32, Fmaf64, Fmaf80, Fmaf128, Fmappcf128,

   Minnumf32, Minnumf64, Minnumf80, Minnumf128, Minnumppcf128,
   Maxnumf32, Maxnumf64, Maxnumf80, Maxnumf128, Maxnumppcf128,
   Minimumf32, Minimumf64, Minimumf80, Minimumf128, Minimumppcf128,
   Maximumf32, Maximumf64, Maximumf80, Maximumf128, Maximumppcf128,
   Copysignf32, Copysignf64, Copysignf80, Copysignf128, Copysignppcf128,


   FirstUnary = Trunc, LastUnary = FNeg,
   FirstCast = Trunc, LastCast = BitCast,
   FirstBinary = Add, LastBinary = LOr,
   FirstUnaryIntr = Sinf32, LastUnaryIntr = Ceilppcf128,     //added by SBH
   FirstBinaryIntr = Powf32, LastBinaryIntr = Copysignppcf128      //added by SBH

  };

protected:
  Op op;
  std::shared_ptr<Type> type;

  /* 
   * Constraint initializes constraint back reference during create() calls.
   * This is a write-once read-many field, so we don't bother with a shared ptr.
   */
  friend class Constraints;
  Constraints *constraint;

public:
  virtual ~Expr() = default;

  void setType(std::shared_ptr<Type> t) { type = t; }
  std::shared_ptr<Type> getType() { return type; }
  Op getOp() const { return op; }
  Constraints* getConstraint() { return constraint; }

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

class IntConstant : public Constant {
  long v;
public:
  IntConstant(long v, std::shared_ptr<Type> t) : v(v) 
      { type = t; op = Expr::Op::None; }
  long getValue() { return v; }           
  void setValue(long val) { v = val; }           
  void accept(ConstraintVisitor * visitor) override; 
};

class FloatConstant : public Constant {
  float v;
public:
  FloatConstant(float v, std::shared_ptr<Type> t) : v(v) 
      { type = t; op = Expr::Op::None; }
  float getValue() { return v; }           
  void setValue(float val) { v = val; }           
  void accept(ConstraintVisitor * visitor) override; 
};

class DoubleConstant : public Constant {
  double v;
public:
  DoubleConstant(double v, std::shared_ptr<Type> t) : v(v) 
      { type = t; op = Expr::Op::None; }
  double getValue() { return v; }           
  void setValue(double val) { v = val; }           
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
  void setChild(int i, std::shared_ptr<Expr> c) { child[i] = c; }
  void accept(ConstraintVisitor * visitor) override;
};

// Binary expressions
class BinaryExpr : public Expr {
  std::shared_ptr<Expr> child[2];
public:
  BinaryExpr(std::shared_ptr<Expr> c1, std::shared_ptr<Expr> c2, Expr::Op o) { op = o; child[0] = c1; child[1] = c2; }
  BinaryExpr(std::shared_ptr<Expr> c1, std::shared_ptr<Expr> c2, Expr::Op o, std::shared_ptr<Type> t)   // added for binary intrinsic
            { op = o; child[0] = c1; child[1] = c2; type = t; }
  std::shared_ptr<Expr> getChild(int i) { return child[i]; }
  void setChild(int i, std::shared_ptr<Expr> c) { child[i] = c; }
  void accept(ConstraintVisitor * visitor) override;
};

/*
 * A constraint is a dictionary of symbols and Boolean expression.
 *
 * TBD: The visibility of these methods should be controlled better.
 * Perhaps use protected and friends for exposing intra-lib API.
 */
class Constraints {
  std::map<std::string, std::string> symbolTypes;
  std::map<std::string, std::string> symbolValues;

  std::map<std::string, std::string> symbolValueMins; // added by SBH
  std::map<std::string, std::string> symbolValueMaxs; // added by SBH
  std::shared_ptr<Expr> expr = nullptr;

  // Recording of interned sub-expressions to reduce redundancy
  std::map<Type::Base, std::map<int, std::shared_ptr<Type>>> internType;
  std::map<std::string, std::shared_ptr<Symbol>> internSymbol;
public:
  std::set<std::string> symbols;


  void defineSymbol(std::string n, std::string t, std::string v, std::string min, std::string max);  //change this method to read a vector of size three // added by SBH




  bool isDefined(std::string n);
  std::string symbolType(std::string n) { return symbolTypes.find(n)->second; }
  std::string symbolValue(std::string n) { return symbolValues.find(n)->second; }

  std::string symbolValueMin(std::string n) { return symbolValueMins.find(n)->second; }   // added by SBH
  std::string symbolValueMax(std::string n) { return symbolValueMaxs.find(n)->second; }   // added by SBH

  void setExpr(std::shared_ptr<Expr> e) { expr = e; }
  std::shared_ptr<Expr> getExpr() { return expr; }

  // Create methods for constraint sub-expressions


  std::shared_ptr<Type> create(Type::Base b, int w);

  std::shared_ptr<Symbol> create(std::string name, std::shared_ptr<Type> t);
  std::shared_ptr<IntConstant> create(long v, std::shared_ptr<Type> t);
  std::shared_ptr<FloatConstant> create(float v, std::shared_ptr<Type> t);
  std::shared_ptr<DoubleConstant> create(double v, std::shared_ptr<Type> t);
  std::shared_ptr<UnaryExpr> create(std::shared_ptr<Expr> c, Expr::Op o);
  std::shared_ptr<UnaryExpr> create(std::shared_ptr<Expr> c, Expr::Op o, std::shared_ptr<Type> t);
  std::shared_ptr<BinaryExpr> create(std::shared_ptr<Expr> c1, std::shared_ptr<Expr> c2, Expr::Op o);
  std::shared_ptr<BinaryExpr> create(std::shared_ptr<Expr> c1, std::shared_ptr<Expr> c2, Expr::Op o, std::shared_ptr<Type> t);  // for Binary Intrinsic Expr

  //added by SBH

  //std::shared_ptr<UnIntrExpr> create(std::shared_ptr<Expr> c, Expr::Op o, std::shared_ptr<Type> t);
  //std::shared_ptr<BinIntrExpr> create(std::shared_ptr<Expr> c1, std::shared_ptr<Expr> c2, Expr::Op o, std::shared_ptr<Type> t);

  // Translation methods for external and internal representations
  std::shared_ptr<Type> str2type(std::string s);
  std::string type2str(std::shared_ptr<Type> t);
  Expr::Op str2op(std::string s);
  std::string op2str(Expr::Op o);
};

std::optional<std::shared_ptr<Constraints>> parse(std::istream& stream);


}
