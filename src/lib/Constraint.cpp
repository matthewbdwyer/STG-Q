#include <algorithm> 
#include <cassert>
#include <sstream>
#include <optional>

#include "Constraint.h"
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

std::optional<std::shared_ptr<Constraint>> parse(std::istream& stream) {
  ANTLRInputStream input(stream);
  ConstraintGrammarLexer lexer(&input);
  CommonTokenStream tokens(&lexer);
  ConstraintGrammarParser parser(&tokens);
  std::shared_ptr<bool> parseError = std::make_shared<bool>(false);
  ErrorListener errorListener(parseError);

  // Add error listeners
  lexer.addErrorListener(&errorListener);
  parser.addErrorListener(&errorListener);

  auto parsetree = parser.constraint();

  if (*parseError) {  
    return std::nullopt;
  }

  ConstraintBuilder cb(&parser);
  return std::make_optional<std::shared_ptr<Constraint>>(cb.build(parsetree));
}

/****************** Constraint Type and Operator Conversions ************/

std::shared_ptr<Type> Constraint::str2type(std::string s) {
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

std::string Constraint::type2str(std::shared_ptr<Type> t) {
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
  {"fult", Expr::Op::FUgt},
  {"fule", Expr::Op::FUge},
  {"fugt", Expr::Op::FUlt},
  {"fuge", Expr::Op::FUle},
  {"funo", Expr::Op::FUno},
  {"land", Expr::Op::LAnd},
  {"lor", Expr::Op::LOr}
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
  {Expr::Op::FUgt, "fult"}, 
  {Expr::Op::FUge, "fule"}, 
  {Expr::Op::FUlt, "fugt"}, 
  {Expr::Op::FUle, "fuge"}, 
  {Expr::Op::FUno, "funo"}, 
  {Expr::Op::LAnd, "land"}, 
  {Expr::Op::LOr, "lor"}
}; 

Expr::Op Constraint::str2op(std::string s) {
  std::map<std::string, Expr::Op>::iterator it;
  it = soMap.find(s);
  if (it == soMap.end()) {
    assert(false && "Invalid string for Constraint::Expr::Op conversion");
  }
  return it->second;
}

std::string Constraint::op2str(Expr::Op o) {
  std::map<Expr::Op, std::string>::iterator it;
  it = osMap.find(o);
  if (it == osMap.end()) {
    assert(false && "Invalid Constraint::Expr::Op for string conversion");
  }
  return it->second;
}

bool Constraint::isDefined(std::string n) {
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

void LongConstant::accept(ConstraintVisitor* visitor) {
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

void Constraint::defineSymbol(std::string n, std::string t, std::string v) {
  symbols.insert(n);
  symbolTypes.insert(std::pair<std::string, std::string>(n, t));
  symbolValues.insert(std::pair<std::string, std::string>(n, v));
}

/*
 * Create methods for constraint subexpressions
 * Symbols and types are interned to save space and make equality tests fast.
 */

std::shared_ptr<Type> Constraint::create(Type::Base b, int w) {
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

std::shared_ptr<Symbol> Constraint::create(std::string n, std::shared_ptr<Type> t) {
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

std::shared_ptr<IntConstant> Constraint::create(int v, std::shared_ptr<Type> t) {
  auto n = std::make_shared<IntConstant>(v, t);
  n->constraint = this;
  return n;
}

std::shared_ptr<LongConstant> Constraint::create(long v, std::shared_ptr<Type> t) {
  auto n = std::make_shared<LongConstant>(v, t);
  n->constraint = this;
  return n;
}

std::shared_ptr<FloatConstant> Constraint::create(float v, std::shared_ptr<Type> t) {
  auto n = std::make_shared<FloatConstant>(v, t);
  n->constraint = this;
  return n;
}

std::shared_ptr<DoubleConstant> Constraint::create(double v, std::shared_ptr<Type> t) {
  auto n = std::make_shared<DoubleConstant>(v, t);
  n->constraint = this;
  return n;
}

std::shared_ptr<UnaryExpr> Constraint::create(std::shared_ptr<Expr> c, Expr::Op o) { 
  auto n = std::make_shared<UnaryExpr>(c,o);
  n->constraint = this;
  return n;
}

std::shared_ptr<UnaryExpr> Constraint::create(std::shared_ptr<Expr> c, Expr::Op o, std::shared_ptr<Type> t) { 
  auto n = std::make_shared<UnaryExpr>(c,o,t);
  n->constraint = this;
  return n;
}

std::shared_ptr<BinaryExpr> Constraint::create(std::shared_ptr<Expr> c1, std::shared_ptr<Expr> c2, Expr::Op o) {
  auto n = std::make_shared<BinaryExpr>(c1,c2,o);
  n->constraint = this;
  return n;
}

}
