#include <algorithm> 
#include <cassert>
#include <sstream>
#include <optional>

#include "Constraint.h"
#include "ConstraintPrinter.h"
#include "ConstraintVisitor.h"
#include "ConstraintGrammarLexer.h"
#include "ConstraintGrammarParser.h"
#include "ConstraintBuilder.h"
#include "antlr4-runtime.h"

using namespace antlr4;

namespace Constraint {

/***************** Parser and Lexer Support **********************/

class ErrorListener : public BaseErrorListener {
  std::shared_ptr<bool> error;
public:
  ErrorListener(std::shared_ptr<bool> e) : error(e) {}

  void syntaxError(Recognizer *recognizer, Token *offendingSymbol, 
                   size_t line, size_t charPositionInLine, 
                   const std::string &msg, std::exception_ptr e) {
    *error = true;
  }
};

std::optional<std::shared_ptr<Constraints>> parse(std::istream& stream) {
  ANTLRInputStream input(stream);
  ConstraintGrammarLexer lexer(&input);
  CommonTokenStream tokens(&lexer);
  ConstraintGrammarParser parser(&tokens);
  std::shared_ptr<bool> parseError = std::make_shared<bool>(false);
  ErrorListener errorListener(parseError);

  // Add error listeners
  lexer.addErrorListener(&errorListener);
  parser.addErrorListener(&errorListener);


  //std::cout<<"here we are, yoooooooo\n";

  auto parsetree = parser.constraint();

  if (*parseError) {  
    return std::nullopt;
  }

  //std::cout<<"here we are\n";
  ConstraintBuilder cb(&parser);


  auto de = cb.build(parsetree);
  // ConstraintPrinter cp(std::cout, 2);
  // cp.print(de);

  return std::make_optional<std::shared_ptr<Constraints>>(cb.build(parsetree));
}

/****************** Constraint Type and Operator Conversions ************/

std::shared_ptr<Type> Constraints::str2type(std::string s) {
  if (s[0] == 'i') {
    int width = std::stoi(s.substr(1,s.length()-1));
    return create(Type::Base::Int, width);
  } else if (s.substr(0,5) == "float") {
    return create(Type::Base::Float, 32);
  } else if (s.substr(0,6) == "double") {
    return create(Type::Base::Float, 64);
  }
  assert(false && "Invalid Constraint::Type for string");
}

std::string Constraints::type2str(std::shared_ptr<Type> t) {
  if (t->getBase() == Type::Base::Int) {
    return "i" + std::to_string(t->getWidth());
  } else if (t->getBase() == Type::Base::Float) {
    if (t->getWidth() == 32) {
      return "float";
    } else if (t->getWidth() == 64) {
      return "double";
    } 
    assert(false && "Invalid width for Constraint::Type::Base::Float");
  }
  assert(false && "Invalid Constraint::Type::Base");
}

/* 
 * A pair of lookup tables for mapping between operators and ther 
 * string representations in the grammar.
 * Coordinate any changes between the two.
 */
std::map<std::string, Expr::Op> soMap = {
  {"trunc", Expr::Op::Trunc},
  {"zext", Expr::Op::ZExt},
  {"sext", Expr::Op::SExt},
  {"uitofp", Expr::Op::UItoFP},
  {"sitofp", Expr::Op::SItoFP},
  {"fptrunc", Expr::Op::FPTrunc},
  {"fpext", Expr::Op::FPExt},
  {"fptoui", Expr::Op::FPtoUI},
  {"fptosi", Expr::Op::FPtoSI},
  {"bitcast", Expr::Op::BitCast},
  {"lnot", Expr::Op::LNot},
  {"fneg", Expr::Op::FNeg},
  {"add", Expr::Op::Add},
  {"sub", Expr::Op::Sub},
  {"mul", Expr::Op::Mul},
  {"udiv", Expr::Op::UDiv},
  {"sdiv", Expr::Op::SDiv},
  {"urem", Expr::Op::URem},
  {"srem", Expr::Op::SRem},
  {"fadd", Expr::Op::FAdd},
  {"fsub", Expr::Op::FSub},
  {"fmul", Expr::Op::FMul},
  {"fdiv", Expr::Op::FDiv},
  {"frem", Expr::Op::FRem},
  {"and", Expr::Op::And},
  {"or", Expr::Op::Or},
  {"xor", Expr::Op::Xor},
  {"shl", Expr::Op::Shl},
  {"lshr", Expr::Op::LShr},
  {"ashr", Expr::Op::AShr},
  {"eq", Expr::Op::Eq},
  {"ne", Expr::Op::Ne},
  {"ult", Expr::Op::Ult},
  {"ule", Expr::Op::Ule},
  {"ugt", Expr::Op::Ugt},
  {"uge", Expr::Op::Uge},
  {"slt", Expr::Op::Slt},
  {"sle", Expr::Op::Sle},
  {"sgt", Expr::Op::Sgt},
  {"sge", Expr::Op::Sge},
  {"oeq", Expr::Op::FOEq},
  {"one", Expr::Op::FONe},
  {"olt", Expr::Op::FOlt},
  {"ole", Expr::Op::FOle},
  {"ogt", Expr::Op::FOgt},
  {"oge", Expr::Op::FOge},
  {"ord", Expr::Op::FOrd},
  {"fueq", Expr::Op::FUEq},
  {"fune", Expr::Op::FUNe},
  {"fult", Expr::Op::FUlt},
  {"fule", Expr::Op::FUle},
  {"fugt", Expr::Op::FUgt},
  {"fuge", Expr::Op::FUge},
  {"funo", Expr::Op::FUno},
  {"land", Expr::Op::LAnd},
  {"lor", Expr::Op::LOr},
  //added by SBH

  {"llvm.sin.f32",Expr::Op::Sinf32},
  {"llvm.sin.f64",Expr::Op::Sinf64},
  {"llvm.sin.f80",Expr::Op::Sinf80},
  {"llvm.sin.f128",Expr::Op::Sinf128},
  {"llvm.sin.ppcf128",Expr::Op::Sinppcf128},

  {"llvm.cos.f32",Expr::Op::Cosf32},
  {"llvm.cos.f64",Expr::Op::Cosf64},
  {"llvm.cos.f80",Expr::Op::Cosf80},
  {"llvm.cos.f128",Expr::Op::Cosf128},
  {"llvm.cos.ppcf128",Expr::Op::Cosppcf128},

  {"tan.f32", Expr::Op::tanf32},

  {"llvm.exp.f32",Expr::Op::Expf32},
  {"llvm.exp.f64",Expr::Op::Expf64},
  {"llvm.exp.f80",Expr::Op::Expf80},
  {"llvm.exp.f128",Expr::Op::Expf128},
  {"llvm.exp.ppcf128",Expr::Op::Expppcf128},

  {"llvm.exp2.f32",Expr::Op::Exp2f32,},
  {"llvm.exp2.f64",Expr::Op::Exp2f64},
  {"llvm.exp2.f80",Expr::Op::Exp2f80},
  {"llvm.exp2.f128",Expr::Op::Exp2f128},
  {"llvm.exp2.ppcf128",Expr::Op::Exp2ppcf128},

  {"llvm.log.f32",Expr::Op::Logf32},
  {"llvm.log.f64",Expr::Op::Logf64},
  {"llvm.log.f80",Expr::Op::Logf80},
  {"llvm.log.f128",Expr::Op::Logf128},
  {"llvm.log.ppcf128",Expr::Op::Logppcf128},

  {"llvm.log2.f32",Expr::Op::Log2f32},
  {"llvm.log2.f64",Expr::Op::Log2f64},
  {"llvm.log2.f80",Expr::Op::Log2f80},
  {"llvm.log2.f128",Expr::Op::Log2f128},
  {"llvm.log2.ppcf128",Expr::Op::Log2ppcf128},

  {"llvm.log10.f32",Expr::Op::Log10f32},
  {"llvm.log10.f64",Expr::Op::Log10f64},
  {"llvm.log10.f80",Expr::Op::Log10f80},
  {"llvm.log10.f128",Expr::Op::Log10f128},
  {"llvm.log10.ppcf128",Expr::Op::Log10ppcf128},

  {"llvm.fabs.f32",Expr::Op::Fabsf32},
  {"llvm.fabs.f64",Expr::Op::Fabsf64},
  {"llvm.fabs.f80",Expr::Op::Fabsf80},
  {"llvm.fabs.f128",Expr::Op::Fabsf128},
  {"llvm.fabs.ppcf128",Expr::Op::Fabsppcf128},

  {"llvm.sqrt.f32",Expr::Op::Sqrtf32},
  {"llvm.sqrt.f64",Expr::Op::Sqrtf64},
  {"llvm.sqrt.f80",Expr::Op::Sqrtf80},
  {"llvm.sqrt.f128",Expr::Op::Sqrtf128},
  {"llvm.sqrt.ppcf128",Expr::Op::Sqrtppcf128},

  {"llvm.floor.f32",Expr::Op::Floorf32},
  {"llvm.floor.f64",Expr::Op::Floorf64},
  {"llvm.floor.f80",Expr::Op::Floorf80},
  {"llvm.floor.f128",Expr::Op::Floorf128},
  {"llvm.floor.ppcf128",Expr::Op::Floorppcf128},

  {"llvm.ceil.f32",Expr::Op::Ceilf32},
  {"llvm.ceil.f64",Expr::Op::Ceilf64},
  {"llvm.ceil.f80",Expr::Op::Ceilf80},
  {"llvm.ceil.f128",Expr::Op::Ceilf128},
  {"llvm.ceil.ppcf128",Expr::Op::Ceilppcf128},

   // Binary [SBH]
  {"llvm.pow.f32",Expr::Op::Powf32},
  {"llvm.pow.f64",Expr::Op::Powf64},
  {"llvm.pow.f80",Expr::Op::Powf80},
  {"llvm.pow.f128",Expr::Op::Powf128},
  {"llvm.pow.ppcf128",Expr::Op::Powppcf128},

  {"atan2.f32", Expr::Op::atan2f32},

  {"llvm.powi.f32",Expr::Op::Powif32},
  {"llvm.powi.f64",Expr::Op::Powif64},
  {"llvm.powi.f80",Expr::Op::Powif80},
  {"llvm.powi.f128",Expr::Op::Powif128},
  {"llvm.powi.ppcf128",Expr::Op::Powippcf128},

  {"llvm.fma.f32",Expr::Op::Fmaf32},
  {"llvm.fma.f64",Expr::Op::Fmaf64},
  {"llvm.fma.f80",Expr::Op::Fmaf80},
  {"llvm.fma.f128",Expr::Op::Fmaf128},
  {"llvm.fma.ppcf128",Expr::Op::Fmappcf128},

  {"llvm.minnum.f32",Expr::Op::Minnumf32},
  {"llvm.minnum.f64",Expr::Op::Minnumf64},
  {"llvm.minnum.f80",Expr::Op::Minnumf80},
  {"llvm.minnum.f128",Expr::Op::Minnumf128},
  {"llvm.minnum.ppcf128",Expr::Op::Minnumf128},

  {"llvm.maxnum.f32",Expr::Op::Maxnumf32},
  {"llvm.maxnum.f64",Expr::Op::Maxnumf64},
  {"llvm.maxnum.f80",Expr::Op::Maxnumf80},
  {"llvm.maxnum.f128",Expr::Op::Maxnumf128},
  {"llvm.maxnum.ppcf128",Expr::Op::Maxnumppcf128},

  {"llvm.minimum.f32",Expr::Op::Minimumf32},
  {"llvm.minimum.f64",Expr::Op::Minimumf64},
  {"llvm.minimum.f80",Expr::Op::Minimumf80},
  {"llvm.minimum.f128",Expr::Op::Minimumf128},
  {"llvm.minimum.ppcf128",Expr::Op::Minimumppcf128},


  {"llvm.maximum.f32",Expr::Op::Maximumf32},
  {"llvm.maximum.f64",Expr::Op::Maximumf64},
  {"llvm.maximum.f80",Expr::Op::Maximumf80},
  {"llvm.maximum.f128",Expr::Op::Maximumf128},
  {"llvm.maximum.ppcf128",Expr::Op::Maximumppcf128},


  {"llvm.copysign.f32",Expr::Op::Copysignf32},
  {"llvm.copysign.f64",Expr::Op::Copysignf64},
  {"llvm.copysign.f80",Expr::Op::Copysignf80},
  {"llvm.copysign.f128",Expr::Op::Copysignf128},
  {"llvm.copysign.ppcf128",Expr::Op::Copysignppcf128},

  {"sin",Expr::Op::Sin},
  {"cos",Expr::Op::Cos},
  {"tan",Expr::Op::Tan},
  {"log",Expr::Op::Log},
  {"log10f",Expr::Op::Log10f},
  {"log2f",Expr::Op::Log2f},
  {"sqrt",Expr::Op::Sqrt},
  {"pow",Expr::Op::Pow},
  {"exp",Expr::Op::Exp},
  {"expf",Expr::Op::Expf}

};

std::map<Expr::Op, std::string> osMap = {
  {Expr::Op::Trunc, "trunc"}, 
  {Expr::Op::ZExt, "zext"}, 
  {Expr::Op::SExt, "sext"}, 
  {Expr::Op::UItoFP, "uitofp"}, 
  {Expr::Op::SItoFP, "sitofp"}, 
  {Expr::Op::FPTrunc, "fptrunc"}, 
  {Expr::Op::FPExt, "fpext"}, 
  {Expr::Op::FPtoUI, "fptoui"}, 
  {Expr::Op::FPtoSI, "fptosi"}, 
  {Expr::Op::BitCast, "bitcast"}, 
  {Expr::Op::LNot, "lnot"}, 
  {Expr::Op::FNeg, "fneg"}, 
  {Expr::Op::Add, "add"}, 
  {Expr::Op::Sub, "sub"}, 
  {Expr::Op::Mul, "mul"}, 
  {Expr::Op::UDiv, "udiv"}, 
  {Expr::Op::SDiv, "sdiv"}, 
  {Expr::Op::URem, "urem"}, 
  {Expr::Op::SRem, "srem"}, 
  {Expr::Op::FAdd, "fadd"}, 
  {Expr::Op::FSub, "fsub"}, 
  {Expr::Op::FMul, "fmul"}, 
  {Expr::Op::FDiv, "fdiv"}, 
  {Expr::Op::FRem, "frem"}, 
  {Expr::Op::And, "and"}, 
  {Expr::Op::Or, "or"}, 
  {Expr::Op::Xor, "xor"}, 
  {Expr::Op::Shl, "shl"}, 
  {Expr::Op::LShr, "lshr"}, 
  {Expr::Op::AShr, "ashr"}, 
  {Expr::Op::Eq, "eq"}, 
  {Expr::Op::Ne, "ne"}, 
  {Expr::Op::Ult, "ult"}, 
  {Expr::Op::Ule, "ule"}, 
  {Expr::Op::Ugt, "ugt"}, 
  {Expr::Op::Uge, "uge"}, 
  {Expr::Op::Slt, "slt"}, 
  {Expr::Op::Sle, "sle"}, 
  {Expr::Op::Sgt, "sgt"}, 
  {Expr::Op::Sge, "sge"}, 
  {Expr::Op::FOEq, "oeq"}, 
  {Expr::Op::FONe, "one"}, 
  {Expr::Op::FOlt, "olt"}, 
  {Expr::Op::FOle, "ole"}, 
  {Expr::Op::FOgt, "ogt"}, 
  {Expr::Op::FOge, "oge"}, 
  {Expr::Op::FOrd, "ord"}, 
  {Expr::Op::FUEq, "fueq"}, 
  {Expr::Op::FUNe, "fune"}, 
  {Expr::Op::FUgt, "fugt"}, 
  {Expr::Op::FUge, "fuge"}, 
  {Expr::Op::FUlt, "fult"}, 
  {Expr::Op::FUle, "fule"}, 
  {Expr::Op::FUno, "funo"}, 
  {Expr::Op::LAnd, "land"}, 
  {Expr::Op::LOr, "lor"},


  //added by SBH

  {Expr::Op::Sinf32,"llvm.sin.f32"},
  {Expr::Op::Sinf64,"llvm.sin.f64"},
  {Expr::Op::Sinf80,"llvm.sin.f80"},
  {Expr::Op::Sinf128,"llvm.sin.f128"},
  {Expr::Op::Sinppcf128,"llvm.sin.ppcf128"},

  {Expr::Op::Cosf32,"llvm.cos.f32"},
  {Expr::Op::Cosf64,"llvm.cos.f64"},
  {Expr::Op::Cosf80,"llvm.cos.f80"},
  {Expr::Op::Cosf128,"llvm.cos.f128"},
  {Expr::Op::Cosppcf128,"llvm.cos.ppcf128"},

  {Expr::Op::tanf32, "tan.f32"},

  {Expr::Op::Expf32,"llvm.exp.f32"},
  {Expr::Op::Expf64,"llvm.exp.f64"},
  {Expr::Op::Expf80,"llvm.exp.f80"},
  {Expr::Op::Expf128,"llvm.exp.f128"},
  {Expr::Op::Expppcf128,"llvm.exp.ppcf128"},

  {Expr::Op::Exp2f32,"llvm.exp2.f32"},
  {Expr::Op::Exp2f64,"llvm.exp2.f64"},
  {Expr::Op::Exp2f80,"llvm.exp2.f80"},
  {Expr::Op::Exp2f128,"llvm.exp2.f128"},
  {Expr::Op::Exp2ppcf128,"llvm.exp2.ppcf128"},

  {Expr::Op::Logf32,"llvm.log.f32"},
  {Expr::Op::Logf64,"llvm.log.f64"},
  {Expr::Op::Logf80,"llvm.log.f80"},
  {Expr::Op::Logf128,"llvm.log.f128"},
  {Expr::Op::Logppcf128,"llvm.log.ppcf128"},

  {Expr::Op::Log2f32,"llvm.log2.f32"},
  {Expr::Op::Log2f64,"llvm.log2.f64"},
  {Expr::Op::Log2f80,"llvm.log2.f80"},
  {Expr::Op::Log2f128,"llvm.log2.f128"},
  {Expr::Op::Log2ppcf128,"llvm.log2.ppcf128"},

  {Expr::Op::Log10f32,"llvm.log10.f32"},
  {Expr::Op::Log10f64,"llvm.log10.f64"},
  {Expr::Op::Log10f80,"llvm.log10.f80"},
  {Expr::Op::Log10f128,"llvm.log10.f128"},
  {Expr::Op::Log10ppcf128,"llvm.log10.ppcf128"},

  {Expr::Op::Fabsf32,"llvm.fabs.f32"},
  {Expr::Op::Fabsf64,"llvm.fabs.f64"},
  {Expr::Op::Fabsf80,"llvm.fabs.f80"},
  {Expr::Op::Fabsf128,"llvm.fabs.f128"},
  {Expr::Op::Fabsppcf128,"llvm.fabs.ppcf128"},

  {Expr::Op::Sqrtf32,"llvm.sqrt.f32"},
  {Expr::Op::Sqrtf64,"llvm.sqrt.f64"},
  {Expr::Op::Sqrtf80,"llvm.sqrt.f80"},
  {Expr::Op::Sqrtf128,"llvm.sqrt.f128"},
  {Expr::Op::Sqrtppcf128,"llvm.sqrt.ppcf128"},

  {Expr::Op::Floorf32,"llvm.floor.f32"},
  {Expr::Op::Floorf64,"llvm.floor.f64"},
  {Expr::Op::Floorf80,"llvm.floor.f80"},
  {Expr::Op::Floorf128,"llvm.floor.f128"},
  {Expr::Op::Floorppcf128,"llvm.floor.ppcf128"},

  {Expr::Op::Ceilf32,"llvm.ceil.f32"},
  {Expr::Op::Ceilf64,"llvm.ceil.f64"},
  {Expr::Op::Ceilf80,"llvm.ceil.f80"},
  {Expr::Op::Ceilf128,"llvm.ceil.f128"},
  {Expr::Op::Ceilppcf128,"llvm.ceil.ppcf128"},

  // Binary [SBh]

  {Expr::Op::Powf32,"llvm.pow.f32"},
  {Expr::Op::Powf64,"llvm.pow.f64"},
  {Expr::Op::Powf80,"llvm.pow.f80"},
  {Expr::Op::Powf128,"llvm.pow.f128"},
  {Expr::Op::Powppcf128,"llvm.pow.ppcf128"},

  {Expr::Op::atan2f32, "atan2.f32"},

  {Expr::Op::Powif32,"llvm.powi.f32"},
  {Expr::Op::Powif64,"llvm.powi.f64"},
  {Expr::Op::Powif80,"llvm.powi.f80"},
  {Expr::Op::Powif128,"llvm.powi.f128"},
  {Expr::Op::Powippcf128,"llvm.powi.ppcf128"},

  {Expr::Op::Fmaf32,"llvm.fma.f32"},
  {Expr::Op::Fmaf64,"llvm.fma.f64"},
  {Expr::Op::Fmaf80,"llvm.fma.f80"},
  {Expr::Op::Fmaf128,"llvm.fma.f128"},
  {Expr::Op::Fmappcf128,"llvm.fma.ppcf128"},

  {Expr::Op::Minnumf32,"llvm.minnum.f32"},
  {Expr::Op::Minnumf64,"llvm.minnum.f64"},
  {Expr::Op::Minnumf80,"llvm.minnum.f80"},
  {Expr::Op::Minnumf128,"llvm.minnum.f128"},
  {Expr::Op::Minnumf128,"llvm.minnum.ppcf128"},

  {Expr::Op::Maxnumf32,"llvm.maxnum.f32"},
  {Expr::Op::Maxnumf64,"llvm.maxnum.f64"},
  {Expr::Op::Maxnumf80,"llvm.maxnum.f80"},
  {Expr::Op::Maxnumf128,"llvm.maxnum.f128"},
  {Expr::Op::Maxnumppcf128,"llvm.maxnum.ppcf128"},

  {Expr::Op::Minimumf32,"llvm.minimum.f32"},
  {Expr::Op::Minimumf64,"llvm.minimum.f64"},
  {Expr::Op::Minimumf80,"llvm.minimum.f80"},
  {Expr::Op::Minimumf128,"llvm.minimum.f128"},
  {Expr::Op::Minimumppcf128,"llvm.minimum.ppcf128"},

  {Expr::Op::Maximumf32,"llvm.maximum.f32"},
  {Expr::Op::Maximumf64,"llvm.maximum.f64"},
  {Expr::Op::Maximumf80,"llvm.maximum.f80"},
  {Expr::Op::Maximumf128,"llvm.maximum.f128"},
  {Expr::Op::Maximumppcf128,"llvm.maximum.ppcf128"},

  {Expr::Op::Copysignf32,"llvm.copysign.f32"},
  {Expr::Op::Copysignf64,"llvm.copysign.f64"},
  {Expr::Op::Copysignf80,"llvm.copysign.f80"},
  {Expr::Op::Copysignf128,"llvm.copysign.f128"},
  {Expr::Op::Copysignppcf128,"llvm.copysign.ppcf128"},

  {Expr::Op::Sin,"sin"},
  {Expr::Op::Cos,"cos"},
  {Expr::Op::Tan,"tan"},
  {Expr::Op::Log,"log"},
  {Expr::Op::Log10f,"log10f"},
  {Expr::Op::Log2f,"log2f"},
  {Expr::Op::Sqrt,"sqrt"},
  {Expr::Op::Pow,"pow",},
  {Expr::Op::Exp,"exp"},
  {Expr::Op::Expf, "expf"}
  
}; 

Expr::Op Constraints::str2op(std::string s) {
  std::map<std::string, Expr::Op>::iterator it;
  it = soMap.find(s);
  if (it == soMap.end()) {
    assert(false && "Invalid string for Constraint::Expr::Op conversion");
  }
  return it->second;
}

std::string Constraints::op2str(Expr::Op o) {
  std::map<Expr::Op, std::string>::iterator it;
  it = osMap.find(o);
  if (it == osMap.end()) {
    assert(false && "Invalid Constraint::Expr::Op for string conversion");
  }
  return it->second;
}

bool Constraints::isDefined(std::string n) {
   return symbols.find(n) != symbols.end();
}

/* 
 * Generic accept methods 
 * - determine whether to visit the substructure of this node through the "visit(this)" callback
 * - if so, they accept the sub-expression comprising the substructure
 * - finally, they invoke the "endVisit(this)" callback
 */

void Symbol::accept(ConstraintVisitor* visitor) {
  bool b = visitor->visit(this); 
  visitor->endVisit(this); 
}    

void IntConstant::accept(ConstraintVisitor* visitor) {
  bool b = visitor->visit(this); 
  visitor->endVisit(this);
}    

void FloatConstant::accept(ConstraintVisitor* visitor) {
  bool b = visitor->visit(this); 
  visitor->endVisit(this);
}    

void DoubleConstant::accept(ConstraintVisitor* visitor) {
  bool b = visitor->visit(this); 
  visitor->endVisit(this);
}    

void UnaryExpr::accept(ConstraintVisitor* visitor) {
  if (visitor->visit(this)) {
    getChild(0)->accept(visitor);
  }
  visitor->endVisit(this);
}    

void BinaryExpr::accept(ConstraintVisitor* visitor) {
  if (visitor->visit(this)) {
    getChild(0)->accept(visitor);
    getChild(1)->accept(visitor);
  }
  visitor->endVisit(this);
}    

/*
 * Constraint symbol definition and sub-expression create routines
 */

void Constraints::defineSymbol(std::string n, std::string t) {  // changed by Rishab std::string v
  symbols.insert(n);
  symbolTypes.insert(std::pair<std::string, std::string>(n, t));
  // symbolValues.insert(std::pair<std::string, std::string>(n, v));
  // symbolRanges[n] = std::pair<std::string, std::string> (min, max); // Added by Rishab

  // Added by Rishab to support distributions
  // distributions[n] = distribution;
  // params[n] = std::pair<std::string, std::string> (param1, param2);
}

/*
 * Create methods for constraint subexpressions
 * Symbols and types are interned to save space and make equality tests fast.
 */

std::shared_ptr<Type> Constraints::create(Type::Base b, int w) {
  std::map<Type::Base, std::map<int, std::shared_ptr<Type>>>::iterator it;
  it = internType.find(b);
  if (it != internType.end()) {
    std::map<int, std::shared_ptr<Type>> intTypeMap = it->second;
    std::map<int, std::shared_ptr<Type>>::iterator itit;
    itit = intTypeMap.find(w);
    if (itit != intTypeMap.end()) {
      auto sym = std::dynamic_pointer_cast<Type>(itit->second); 
      assert(sym);
      return sym;
    }
 
    // Update inner map
    auto sym = std::make_shared<Type>(b, w);
    intTypeMap.insert(std::pair<int, std::shared_ptr<Type>>(w,sym));
    return sym;
    
  } else {
    // Update outer map 
    std::map<int, std::shared_ptr<Type>> intTypeMap;
    internType.insert(std::pair<Type::Base, std::map<int, std::shared_ptr<Type>>>(b,intTypeMap));

    // Update inner map
    auto sym = std::make_shared<Type>(b, w);
    intTypeMap.insert(std::pair<int, std::shared_ptr<Type>>(w,sym));
    return sym;
  }
}

std::shared_ptr<Symbol> Constraints::create(std::string n, std::shared_ptr<Type> t) {
  std::map<std::string, std::shared_ptr<Symbol>>::iterator it;
  it = internSymbol.find(n);
  if (it != internSymbol.end()) {
    auto sym = std::dynamic_pointer_cast<Symbol>(it->second); 
    assert(sym);
    return sym;
  } else {
    auto sym = std::make_shared<Symbol>(n, t);
    sym->constraint = this;
    internSymbol.insert(std::pair<std::string, std::shared_ptr<Symbol>>(n,sym));
    return sym;
  }
}

std::shared_ptr<IntConstant> Constraints::create(long v, std::shared_ptr<Type> t) {
  auto n = std::make_shared<IntConstant>(v, t);
  n->constraint = this;
  return n;
}

std::shared_ptr<FloatConstant> Constraints::create(float v, std::shared_ptr<Type> t) {
  auto n = std::make_shared<FloatConstant>(v, t);
  n->constraint = this;
  return n;
}

std::shared_ptr<DoubleConstant> Constraints::create(double v, std::shared_ptr<Type> t) {
  auto n = std::make_shared<DoubleConstant>(v, t);
  n->constraint = this;
  return n;
}

std::shared_ptr<UnaryExpr> Constraints::create(std::shared_ptr<Expr> c, Expr::Op o) {
  auto n = std::make_shared<UnaryExpr>(c,o);
  n->constraint = this;
  return n;
}

std::shared_ptr<UnaryExpr> Constraints::create(std::shared_ptr<Expr> c, Expr::Op o, std::shared_ptr<Type> t) {
  auto n = std::make_shared<UnaryExpr>(c,o,t);
  n->constraint = this;
  return n;
}

std::shared_ptr<BinaryExpr> Constraints::create(std::shared_ptr<Expr> c1, std::shared_ptr<Expr> c2, Expr::Op o) {
  auto n = std::make_shared<BinaryExpr>(c1,c2,o);
  n->constraint = this;
  return n;
}

//added by SBH for binary intrinsic
std::shared_ptr<BinaryExpr> Constraints::create(std::shared_ptr<Expr> c1, std::shared_ptr<Expr> c2, Expr::Op o, std::shared_ptr<Type> t) {
  auto n = std::make_shared<BinaryExpr>(c1,c2,o,t);
  n->constraint = this;
  return n;
}

}
