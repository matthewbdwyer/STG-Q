#include "SMTPrinter.h"
#include <jsoncpp/json/json.h>
#include <unordered_set>

using namespace Constraint;

std::unordered_set <std::string> dict_set; 
bool no_var = true;
std::map<std::string, std::string> mapping = {

{"fneg", ""},
{"fptosi", "(to_int "},

{"trunc", ""},
{"zext", ""},
{"sext", ""},
{"fptrunc", ""},
{"fpext", ""},

{"sitofp", "(to_real "},
{"add", "(+ "},
{"sub", "(- "},
{"mul", "(* "},
{"sdiv", "(/ "},
{"srem", "(% "},
{"fadd", "(+ "},
{"fsub", "(- "},
{"fmul", "(* "},
{"fdiv", "(/ "},
{"frem", "(% "},

{"eq", "(= "},
{"ne", "(not(= "},
{"slt", "(< "},
{"sle", "(<= "},
{"sgt", "(> "},
{"sge", "(>= "},
{"oeq", "(= "},
{"one", "(not(= "},
{"fune", "(not(= "},      // Newly added
{"olt", "(< "},
{"ole", "(<= "},
{"ogt", "(> "},
{"oge", "(>= "},


{"land", "(and "},
{"or", "(or "},
{"lnot", "(not "},

//Intrinsics UNARY

{"llvm.sin.f32", "(sin "},
{"llvm.sin.f64", "(sin "},
// {"llvm.sin.f80", "(sin "},
// {"llvm.sin.f128", "(sin "},

{"llvm.cos.f32", "(cos "},
{"llvm.cos.f64", "(cos "},
// {"llvm.cos.f80", "(cos "},
// {"llvm.cos.f128", "(cos "},

{"llvm.tan.f32", "(tan "},
{"llvm.tan.f64", "(tan "},

{"llvm.exp.f32", "(^ EXP "},
{"llvm.exp.f64", "(^ EXP "},
{"llvm.exp.f80", "(^ EXP "},
{"llvm.exp.f128", "(^ EXP "},

{"llvm.log.f32", "(log "},
{"llvm.log.f64", "(log "},
{"llvm.log.f80", "(log "},
{"llvm.log.f128", "(log "},

{"llvm.log10.f32", "(log10 "},
{"llvm.log10.f64", "(log10 "},
{"llvm.log10.f80", "(log10 "},
{"llvm.log10.f128", "(log10 "},

{"llvm.sqrt.f32", "(^ "},
{"llvm.sqrt.f64", "(^ "},
{"llvm.sqrt.f80", "(^ "},
{"llvm.sqrt.f128", "(^ "},

{"llvm.exp2.f32", "(^ 2.0 "},
{"llvm.exp2.f64", "(^ 2.0 "},
{"llvm.exp2.f80", "(^ 2.0 "},
{"llvm.exp2.f128", "(^ 2.0 "},

//New functions added for testing

// {"llvm.floor.f32", "ASDOUBLE("},
// {"llvm.floor.f64", "ASDOUBLE("},
// {"llvm.floor.f80", "ASDOUBLE("},
// {"llvm.floor.f128", "ASDOUBLE("},

// {"llvm.ceil.f32", "ASDOUBLE("},
// {"llvm.ceil.f64", "ASDOUBLE("},
// {"llvm.ceil.f80", "ASDOUBLE("},
// {"llvm.ceil.f128", "ASDOUBLE("},

// {"llvm.fabs.f32", "ADD("},
// {"llvm.fabs.f64", "ADD("},
// {"llvm.fabs.f80", "ADD("},
// {"llvm.fabs.f128", "ADD("},

//Intrinsics BINARY

{"llvm.pow.f32", "(^ "},
{"llvm.pow.f64", "(^ "},
{"llvm.pow.f80", "(^ "},
{"llvm.pow.f128", "(^ "},

{"llvm.minnum.f32", "(min "},
{"llvm.minnum.f64", "(min "},
{"llvm.minnum.f80", "(min "},
{"llvm.minnum.f128", "(min "},

{"llvm.maxnum.f32", "(max "},
{"llvm.maxnum.f64", "(max "},
{"llvm.maxnum.f80", "(max "},
{"llvm.maxnum.f128", "(max "},

{"llvm.minimum.f32", "(min "},
{"llvm.minimum.f64", "(min "},
{"llvm.minimum.f80", "(min "},
{"llvm.minimum.f128", "(min "},

{"llvm.maximum.f32", "(max "},
{"llvm.maximum.f64", "(max "},
{"llvm.maximum.f80", "(max "},
{"llvm.maximum.f128", "(max "}

};


void SMTPrinter::parseDict(const char *dict, std::shared_ptr<Constraint::Constraints> c, std::string var) {

  Json::Value root;
  std::ifstream ifs;
  ifs.open(std::string(dict));
  ifs >> root;

  Json::Value data = root[var];

  if(data.isNull()){
    std::cerr<<"No data available for: "<< var<<"\n";
    return;
  }

  std::string distribution = data["distribution"].asString();
  
  if(distribution.empty()){
    std::cerr<<"No distribution set for: "<< var <<". Setting default distribution (UNIFORM_INT)"<<"\n";
    distribution = "UNIFORM_INT";
  }

  Json::Value range = data["range"];

  if(range.isNull()){
    std::cerr<<"No Range available for: "<< var<<"\n";
    return;
  }

  std::string max = range["max"].asString();

  if(max.empty())
  {
    std::cerr<<"No Max value available for: "<< var<<"\n";
    return;
  }

  std::string min = range["min"].asString();

  if(min.empty())
  {
    std::cerr<<"No min value available for: "<< var<<"\n";
    return;
  }

  if(distribution == "UNIFORM_INT" || distribution == "UNIFORM_REAL"){
    
    if(c->symbolType(var) == "i1")
      os << "(declare-const "<< var << " Bool)";

    else if(c->symbolType(var)[0] == 'i'){
      os<< "(set-info :domain \"" << var <<" UniformInt "<< min<<" "<<max<<"\")\n";
      os << "(declare-const "<< var << " Int)\n";
    }

    else if(c->symbolType(var) == "float" || c->symbolType(var) == "double"){
      os<< "(set-info :domain \"" << var <<" UniformReal "<< min<<" "<<max<<"\")\n";
      os << "(declare-const "<< var << " Real)\n";
    }

    else{
      std::cerr<<"Invalid TYPE!!  --> " << c->symbolType(var);
      return;
    }

  }

  else{
    std::cerr<<"Only Uniform distribution currently available in SMT for: "<< var<<"\n";
    return;
  }

}



void SMTPrinter::print(std::shared_ptr<Constraint::Constraints> c, const char *dict) {
  theConstraint = c;
  // os << "(set-option :print-success false)\n";
  // mvn package assembly:single
  // os << "(set-logic AUFLIRA)\n";
  // os << "(set-option :seed 121314)\n(set-option :partitioning true)\n(set-option :non-linear-counter \"qcoral\")\n";
  os << "(declare-const EXP Real)\n(assert (= EXP 2.71828182846))\n";

  indentLevel++;
  for (auto &n : c->symbols) {
    parseDict(dict, c, n);
    dict_set.insert(n);
    // os << "\n";
  }

  indentLevel--;
  os << "\n";

  os << "(assert  (and ";

  c->getExpr()->accept(this); 
  os << visitResults.back();
  visitResults.pop_back();

  if(no_var)
    os << " (= 1 0)))\n";
  else
    os << " (= 1 1)))\n";

  os.flush();
}

void SMTPrinter::endVisit(Symbol * element) {

  if(dict_set.find(element->getName()) != dict_set.end()){
    std::string name = element->getName();
    visitResults.push_back(name);
    no_var = false;
  }
  else
    visitResults.push_back("\nELEMENT NOT FOUND IN DICTIONARY --> " + element->getName() + "\n");
}

void SMTPrinter::endVisit(IntConstant * element) {
  
  std::string result;

  if(element->getType()->getWidth() == 1 && element->getValue() == 1)           // BCONST(true)
    result = "true";

  else if(element->getType()->getWidth() == 1 && element->getValue() == 0)          // BCONST(false)
    result = "false";

  else
    result = std::to_string(element->getValue()); 

  visitResults.push_back(result);
}

void SMTPrinter::endVisit(FloatConstant * element) {

  std::string result = std::to_string(element->getValue()); 
  visitResults.push_back(result);
}

void SMTPrinter::endVisit(DoubleConstant * element) {

  std::string result = std::to_string(element->getValue()); 
  visitResults.push_back(result);
}

bool SMTPrinter::visit(UnaryExpr * element) {
  indentLevel++;
  return true;
}

void SMTPrinter::endVisit(UnaryExpr * element) {

  std::string result1 = visitResults.back();
  visitResults.pop_back();

  std::string op = theConstraint->op2str(element->getOp());
  std::string result = "";

  if(mapping.find(op) != mapping.end())
    result += mapping[op];
  else{
    std::cerr << "\nUnary key not found..." << op <<"\n";
    return;
  }

  if(op == "fneg")
    result += "-" + result1 + ")";
  else if(op.find("sqrt") != -1)
    result += result1 + " 0.5)";
  else if(mapping[op] != "")
    result += result1 + ")";
  else
    result += result1;

  visitResults.push_back(result);
}       

bool SMTPrinter::visit(BinaryExpr * element) {
  indentLevel++;
  return true;
}

void SMTPrinter::endVisit(BinaryExpr * element) {

  std::string result2 = visitResults.back();
  visitResults.pop_back();
  std::string result1 = visitResults.back();
  visitResults.pop_back();

  std::string op = theConstraint->op2str(element->getOp());
  std::string result = "";

  if( mapping.find(op) != mapping.end())
    result += mapping[op];
  else{
    std::cerr << "\n Binary key not found..." << op <<"\n";
    return;
  }

  if(op == "trunc" || op == "zext" || op == "sext" || op == "fptrunc" || op == "fpext"){
    std::cerr<<" zext came here trunc, zext, sext, fptrunc & fpext in binary expression. This should not happen\n";
    result += result2 + ")";
  }

  else if(op == "ne" || op == "fune" || op == "one")
    result += result1 + " " + result2 + "))";

  else
    result += result1 + " " + result2 + ")";

  visitResults.push_back(result);
}                     

std::string SMTPrinter::indent() const {
  return std::string(indentLevel*indentSize, ' ');
}

