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
    LNot,              // logical not
    FNeg,              // float negation
    // Binary operators
    Add, Sub, Mul, UDiv, SDiv, URem, SRem,       // int arithmetic
    And, Or, Xor, Shl, LShr, AShr,               // bitwise
    Eq, Ne, Ult, Ule, Ugt, Uge, Slt, Sle, Sgt, Sge,  // comparison
    FAdd, FSub, FMul, FDiv, FRem,            // float arithmetic
    FOEq, FONe, FOlt, FOle, FOgt, FOge, FOrd,        // float comparison
    FUEq, FUNe, FUlt, FUle, FUgt, FUge, FUno,        // float comparison
    LAnd, LOr,               // logical

    //added by SBH  for unary llvm intrinsics (Reordered by Rishab)
   
   Sinf32, Cosf32, Expf32, Exp2f32, Logf32, Log2f32, Log10f32, Fabsf32, Sqrtf32, Floorf32, Ceilf32, tanf32,
   Sinf64, Cosf64, Expf64, Exp2f64, Logf64, Log2f64, Log10f64, Fabsf64, Sqrtf64, Floorf64, Ceilf64,
   Sinf80, Cosf80, Expf80, Exp2f80, Logf80, Log2f80, Log10f80, Fabsf80, Sqrtf80, Floorf80, Ceilf80,
   Sinf128, Cosf128, Expf128, Exp2f128, Logf128, Log2f128, Log10f128, Fabsf128, Sqrtf128, Floorf128, Ceilf128,
   Sinppcf128, Cosppcf128, Expppcf128, Exp2ppcf128, Logppcf128, Log2ppcf128, Log10ppcf128, Fabsppcf128, Sqrtppcf128, Floorppcf128, Ceilppcf128,
   Sin, Cos, Tan, Exp, Expf, Log, Log10f, Log2f, Sqrt,

   //added by SBH for binary llvm intrinsics (Reordered by Rishab)

   Powf32, Powif32, Fmaf32, Minnumf32, Maxnumf32, Minimumf32, Maximumf32, Copysignf32, atan2f32, atan2,
   Powf64, Powif64, Fmaf64, Minnumf64, Maxnumf64, Minimumf64, Maximumf64, Copysignf64,
   Powf80, Powif80, Fmaf80, Minnumf80, Maxnumf80, Minimumf80, Maximumf80, Copysignf80,
   Powf128, Powif128, Fmaf128, Minnumf128, Maxnumf128, Minimumf128, Maximumf128, Copysignf128,
   Powppcf128, Powippcf128, Fmappcf128, Minnumppcf128, Maxnumppcf128, Minimumppcf128, Maximumppcf128, Copysignppcf128,
   Pow,

    //added by SBH

    FirstUnary = Trunc, LastUnary = FNeg,
    FirstCast = Trunc, LastCast = BitCast,
    FirstBinary = Add, LastBinary = LOr,
    FirstUnaryIntr = Sinf32, LastUnaryIntr = Sqrt,      //added by SBH   [Need to change]
    FirstBinaryIntr = Powf32, LastBinaryIntr = Pow //added by SBH   [Need to change]

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
  BinaryExpr(std::shared_ptr<Expr> c1, std::shared_ptr<Expr> c2, Expr::Op o)
      { op = o; child[0] = c1; child[1] = c2; }
  BinaryExpr(std::shared_ptr<Expr> c1, std::shared_ptr<Expr> c2, Expr::Op o, std::shared_ptr<Type> t)   // added for binary intrinsic SBH
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

  // std::map<std::string, std::pair<std::string, std::string> > symbolRanges; // Added by Rishab

  // Added by Rishab to support distributions
  // std::map<std::string, std::string> distributions;
  // std::map<std::string, std::pair<std::string, std::string> > params;

  std::shared_ptr<Expr> expr = nullptr;

  // Recording of interned sub-expressions to reduce redundancy
  std::map<Type::Base, std::map<int, std::shared_ptr<Type>>> internType;
  std::map<std::string, std::shared_ptr<Symbol>> internSymbol;
public:
  std::set<std::string> symbols;

  void defineSymbol(std::string n, std::string t); // changed by Rishab    std::string v

  bool isDefined(std::string n);
  std::string symbolType(std::string n) { return symbolTypes.find(n)->second; }
  std::string symbolValue(std::string n) { return symbolValues.find(n)->second; }

  // std::string symbolRange(std::string n) { return (symbolRanges[n].first + " " + symbolRanges[n].second); } // Added by Rishab

  //Added by Rishab to support distributions
  // std::string get_distribution(std::string n) { return distributions[n];}
  // std::pair<std::string, std::string> get_params(std::string n) {return params[n];}

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
  std::shared_ptr<BinaryExpr> create(std::shared_ptr<Expr> c1, std::shared_ptr<Expr> c2, Expr::Op o, std::shared_ptr<Type> t);  // for Binary Intrinsic Expr [SBH]

  // Translation methods for external and internal representations
  std::shared_ptr<Type> str2type(std::string s);
  std::string type2str(std::shared_ptr<Type> t);
  Expr::Op str2op(std::string s);
  std::string op2str(Expr::Op o);
};

std::optional<std::shared_ptr<Constraints>> parse(std::istream& stream);


}
