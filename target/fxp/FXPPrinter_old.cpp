#include "FXPPrinter.h"
#include <jsoncpp/json/json.h>
#include <unordered_set>

using namespace Constraint;

std::unordered_set <std::string> dict_set; 
bool no_var = true;
std::map<std::string, std::string> mapping = {

// {"fneg", "(fp.neg "},
// {"fptosi", ""},    
// {"sitofp", "(ite "},   

// {"trunc", ""},
// {"zext", ""},
// {"sext", ""},
// {"fptrunc", ""},
// {"fpext", ""},

{"add", "(bvadd "},
{"sub", "(bvsub "},
{"mul", "(bvmul "},
{"sdiv", "(bvsdiv "},
{"srem", "(bvsrem "},
{"fadd", "(fxp.add saturation "},
{"fsub", "(fxp.sub saturation "},
{"fmul", "(fxp.mul saturation roundDown "},
{"fdiv", "(fxp.div saturation roundDown "},
// {"frem", "(fxp.rem RNE "},

{"eq", "(= "},
{"ne", "(not(= "},
{"slt", "(bvslt "},
{"sle", "(bvsle "},
{"sgt", "(bvsgt "},
{"sge", "(bvsge "},
{"ult", "(bvult "},
{"ugt", "(bvugt "},
{"ule", "(bvule "},
{"uge", "(bvuge "},
{"oeq", "(= "},
{"one", "(not(= "},
// {"fune", "(not(fp.eq "},      // CHECK
{"olt", "(sfxp.lt "},
{"ole", "(sfxp.leq "},
{"ogt", "(sfxp.gt "},
{"oge", "(sfxp.geq "},


{"land", "(and "},
{"or", "(or "},
{"lnot", "(not "},

//Intrinsics UNARY

// {"llvm.sin.f32", "(ite  "},
// {"llvm.sin.f64", "(ite  "},
// {"llvm.sin.f80", "(sin "},
// {"llvm.sin.f128", "(sin "},

// {"llvm.cos.f32", "(ite "},
// {"llvm.cos.f64", "(ite "},
// {"llvm.cos.f80", "(cos "},
// {"llvm.cos.f128", "(cos "},

// {"llvm.exp.f32", "(^ EXP "},
// {"llvm.exp.f64", "(^ EXP "},
// {"llvm.exp.f80", "(^ EXP "},
// {"llvm.exp.f128", "(^ EXP "},

// {"llvm.log.f32", "(log "},
// {"llvm.log.f64", "(log "},
// {"llvm.log.f80", "(log "},
// {"llvm.log.f128", "(log "},

// {"llvm.log10.f32", "(log10 "},
// {"llvm.log10.f64", "(log10 "},
// {"llvm.log10.f80", "(log10 "},
// {"llvm.log10.f128", "(log10 "},

// {"llvm.sqrt.f32", "(^ "},
// {"llvm.sqrt.f64", "(^ "},
// {"llvm.sqrt.f80", "(^ "},
// {"llvm.sqrt.f128", "(^ "},

// {"llvm.exp2.f32", "(^ ((_ to_fp 8 24) RNE 1.0 1) "},
// {"llvm.exp2.f64", "(^ ((_ to_fp 11 53) RNE 1.0 1) "},
// {"llvm.exp2.f80", "(^ ((_ to_fp 12 68) RNE 1.0 1) "}, 
// {"llvm.exp2.f128", "(^ ((_ to_fp 15 113) RNE 1.0 1) "},

//New functions added for testing

// {"llvm.floor.f32", "(ite "},  // DONE
// {"llvm.floor.f64", "(ite "},
// {"llvm.floor.f80", "(ite "},
// {"llvm.floor.f128", "(ite "},

// {"llvm.ceil.f32", "(ite "},
// {"llvm.ceil.f64", "(ite "},
// {"llvm.ceil.f80", "(ite "},
// {"llvm.ceil.f128", "(ite "},

// {"llvm.fabs.f32", "ADD("},
// {"llvm.fabs.f64", "ADD("},
// {"llvm.fabs.f80", "ADD("},
// {"llvm.fabs.f128", "ADD("},

//Intrinsics BINARY

// {"llvm.pow.f32", "(^ "},
// {"llvm.pow.f64", "(^ "},
// {"llvm.pow.f80", "(^ "},
// {"llvm.pow.f128", "(^ "},

// {"llvm.minnum.f32", "(fp.min "},
// {"llvm.minnum.f64", "(fp.min "},
// {"llvm.minnum.f80", "(fp.min "},
// {"llvm.minnum.f128", "(fp.min "},

// {"llvm.maxnum.f32", "(fp.max"},
// {"llvm.maxnum.f64", "(fp.max"},
// {"llvm.maxnum.f80", "(fp.max"},
// {"llvm.maxnum.f128", "(fp.max"},

// {"llvm.minimum.f32", "(fp.min "},
// {"llvm.minimum.f64", "(fp.min "},
// {"llvm.minimum.f80", "(fp.min "},
// {"llvm.minimum.f128", "(fp.min "},

// {"llvm.maximum.f32", "(fp.max"},
// {"llvm.maximum.f64", "(fp.max"},
// {"llvm.maximum.f80", "(fp.max"},
// {"llvm.maximum.f128", "(fp.max"},

// {"sin","(ite  "},
// {"cos","(ite "},
// {"tan","(ite "},  //(tan (fp.to_real 
// {"log","LOG_("},
// {"log10f","LOG10_("},
// {"sqrt","(fp.sqrt RNE "},

// {"pow","(ite "},  // 2 cases 1 for float and second for double

// {"exp", "((_ to_fp 11 53) RNE (^ EXP (fp.to_real "},    // 3 closing paranthesis required
// {"expf", "((_ to_fp 8 24) RNE (^ EXP (fp.to_real "}     //  ""

};


void FXPPrinter::parseDict(const char *dict, std::shared_ptr<Constraint::Constraints> c, std::string var) {

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
      os << "(declare-fun " << var << " () (_ BitVec " << 1 << "))\n";

    else if(c->symbolType(var)[0] == 'i'){
      int width = stoi(c->symbolType(var).substr(1));
      os << "(set-info :domain \"" << var <<" UniformInt "<< min << " " << max <<"\")\n";
      os << "(declare-fun " << var << " () (_ BitVec " << width << "))\n";
    }

    else if(c->symbolType(var) == "float"){
      os << "(set-info :domain \"" << var <<" UniformReal "<< min <<" "<< max<<"\")\n";
      os << "(declare-fun "<< var << " () (_ SFXP 32 5))\n";
    }

    else if(c->symbolType(var) == "double"){
      os << "(set-info :domain \"" << var <<" UniformReal "<< min <<" "<< max<<"\")\n";
      os << "(declare-fun "<< var << " () (_ SFXP 64 10))\n";
    }

    else{
      std::cerr<<"Invalid TYPE!!  --> " << c->symbolType(var);
      return;
    }

  }

  else{
    std::cerr<<"Only Uniform distribution currently available in BV for: "<< var<<"\n";
    return;
  }

}



void FXPPrinter::print(std::shared_ptr<Constraint::Constraints> c, const char *dict) {
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
  }

  indentLevel--;
  os << "\n";
  os << "(assert  (and ";

  c->getExpr()->accept(this); 

  os << visitResults.back();

  visitResults.pop_back();

  if(no_var)
    os << " (= ((_ sfxp 10) #x016) ((_ sfxp 10) #x017)) ))\n";
  else
    os << " (= ((_ sfxp 10) #x016) ((_ sfxp 10) #x016)) ))\n";

  os.flush();
}

void FXPPrinter::endVisit(Symbol * element) {

  if(dict_set.find(element->getName()) != dict_set.end()){
    std::string name = element->getName();
    visitResults.push_back(name);
    no_var = false;
  }
  else
    visitResults.push_back("\nELEMENT NOT FOUND IN DICTIONARY --> " + element->getName() + "\n");
}

void FXPPrinter::endVisit(IntConstant * element) {
  
  std::string result;

  if(element->getType()->getWidth() == 1 && element->getValue() == 1)           // BCONST(true)
    result = "true";

  else if(element->getType()->getWidth() == 1 && element->getValue() == 0)          // BCONST(false)
    result = "false";

  else{
    // result = "((_ int2bv " + std::to_string(element->getType()->getWidth()) + ") " + std::to_string(element->getValue()) + ")";
    std::stringstream stream;
    stream << std::hex << (int(element->getValue()));

    result = stream.str();
  }

  visitResults.push_back(result);
}

void FXPPrinter::endVisit(FloatConstant * element) {

  std::stringstream stream;
  stream << std::hex << (int(element->getValue()) << 5);

  std::string result = "((_ sfxp 5) " + stream.str() + ")"; 
  visitResults.push_back(result);
}

void FXPPrinter::endVisit(DoubleConstant * element) {

  std::stringstream stream;
  stream << std::hex << (long(element->getValue()) << 10);
  
  std::string result = "((_ sfxp 10) " + stream.str() + ")"; 
  visitResults.push_back(result);
}

bool FXPPrinter::visit(UnaryExpr * element) {
  indentLevel++;
  return true;
}

void FXPPrinter::endVisit(UnaryExpr * element) {
  
  // std::string width = std::to_string(element->getType()->getWidth());
  std::string width = "32";
  std::string t = "32";

  // std::string result_width = std::stoi((visitResults.back())->getWidth()); 
  std::string result_width = "128";

  std::string result1 = visitResults.back();
  visitResults.pop_back();

  std::string op = theConstraint->op2str(element->getOp());
  std::string result = "";

  if(op == "sitofp" || op == "fptosi" || op == "sext" || op == "trunc" || op == "sin" || op == "cos" || op == "tan"){
    t = element->getConstraint()->type2str(element->getType());
    width = (t == "float" ? "32" : "64");
  }

  if(mapping.find(op) != mapping.end())
    result += mapping[op];
  else{
    std::cerr << "\nUnary key not found..." << op <<"\n";
    return;
  }

  if(op == "llvm.sin.f32" || op == "llvm.sin.f64" || op == "llvm.cos.f32" || op == "llvm.cos.f64" || op == "llvm.tan.f32" || op == "llvm.tan.f64")
    op = op.substr(5,3);


  // if(op.find("llvm.floor") != -1)
  //   result += "(> (fp.to_real " + result1 + ") 0) " + "(fp.roundToIntegral RTZ " + result1 + ") (fp.roundToIntegral RTN " + result1 + "))";
  // else if(op.find("llvm.ceil") != -1)
  //   result += "(> (fp.to_real " + result1 + ") 0) " + "(fp.roundToIntegral RTP " + result1 + ") (fp.roundToIntegral RTZ " + result1 + "))";
  // else if(op == "sitofp")
  //   result += "(= " + width + " 32) " + "((_ to_fp 8 24) " + result1 + ") " + "((_ to_fp 11 53) " + result1 + "))";
  // else if(op == "fptosi")
  //   result += "((_ fp.to_sbv " + width + ") RNE " + result1 + ")"; //"(= " + width + " 32) " + "( (_ fp.to_sbv 32) RNE " + result1 + ") ( (_ fp.to_sbv 64) RNE " + result1 + ")";
  if(op == "trunc" || op == "sext"){
    width = (t.substr(1));
    result += "((_ int2bv " + width + ") ((_ bv2int " + result_width + ") " + result1 + "))";
  }
  else if(mapping[op] != "")
    result += result1 + ")";
  else
    result += result1;

  visitResults.push_back(result);
}  



bool FXPPrinter::visit(BinaryExpr * element) {
  indentLevel++;
  return true;
}

void FXPPrinter::endVisit(BinaryExpr * element) {

  std::string width = "";
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

  if(Expr::Op::Powf32 <= element->getOp() && element->getOp() <= Expr::Op::Pow){
    std::string t = element->getConstraint()->type2str(element->getType());
    width = (t == "float" ? "32" : "64");
  }

  if(op == "trunc" || op == "zext" || op == "sext" || op == "fptrunc" || op == "fpext"){
    std::cerr<<" zext came here trunc, zext, sext, fptrunc & fpext in binary expression. This should not happen\n";
    result += result2 + ")";
  }

  else if(op == "ne" || op == "fune" || op == "one")
    result += result1 + " " + result2 + "))";

  // else if(op == "pow")
  //   result += "(= " + width + " 32) " + "((_ to_fp 8 24) RNE (^ (fp.to_real " + result1 + ") (fp.to_real " + result2 + ") )) " + "((_ to_fp 11 53) RNE (^ (fp.to_real " + result1 + ") (fp.to_real " + result2 + ") )))";

  else
    result += result1 + " " + result2 + ")";

  visitResults.push_back(result);

}                     

std::string FXPPrinter::indent() const {
  return std::string(indentLevel*indentSize, ' ');
}
