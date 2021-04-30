#include "FXPPrinter.h"
#include <jsoncpp/json/json.h>
#include <unordered_set>
#include <math.h>
#include <bitset>

using namespace Constraint;

std::unordered_set <std::string> dict_set; 
bool no_var = true; // For checking if any variable is present in the constraint

// Mapping from stg functions to fxp functions.
std::map<std::string, std::string> mapping = {

{"fneg", "(sfxp.neg saturation "},
// {"fptosi", ""},    
// {"sitofp", "(ite "},   

{"trunc", ""},
{"zext", ""},
{"sext", ""},
{"fptrunc", ""},
{"fpext", ""},

{"add", "(sfxp.add saturation "},
{"sub", "(sfxp.sub saturation "},
{"mul", "(sfxp.mul saturation roundDown "},
{"sdiv", "(sfxp.div saturation roundDown "},
// {"srem", "(bvsrem "},
{"fadd", "(sfxp.add saturation "},
{"fsub", "(sfxp.sub saturation "},
{"fmul", "(sfxp.mul saturation roundDown "},
{"fdiv", "(sfxp.div saturation roundDown "},
// {"frem", "(fxp.rem RNE "},

{"eq", "(= "},
{"ne", "(not(= "},
{"slt", "(sfxp.lt "},
{"sle", "(sfxp.leq "},
{"sgt", "(sfxp.gt "},
{"sge", "(sfxp.geq "},

{"ult", "(ufxp.lt "},
{"ugt", "(ufxp.gt "},
{"ule", "(ufxp.leq "},
{"uge", "(ufxp.geq "},

{"oeq", "(= "},
{"one", "(not(= "},
// {"fune", "(not(fp.eq "},
{"olt", "(sfxp.lt "},
{"ole", "(sfxp.leq "},
{"ogt", "(sfxp.gt "},
{"oge", "(sfxp.geq "},


{"land", "(and "},
{"or", "(or "},
{"lnot", "(not "},


};


// Function for parsing dictionary for a specific variable.
void FXPPrinter::parseDict(const char *dict, std::shared_ptr<Constraint::Constraints> c, std::string var) {

  Json::Value root;
  std::ifstream ifs;
  ifs.open(std::string(dict));
  ifs >> root;

  Json::Value data = root[var];

  // Checking if data for the variable is available in the dictionary. If not then exit.
  if(data.isNull()){
    std::cerr<<"No data available for: "<< var<<"\n";
    return;
  }

  std::string distribution = data["distribution"].asString();
  
  // Checking if the distribution data is available for the variable. If not then default to Uniform Distribution.
  if(distribution.empty()){
    std::cerr<<"No distribution set for: "<< var <<". Setting default distribution (UNIFORM_INT)"<<"\n";
    distribution = "UNIFORM_INT";
  }

  Json::Value range = data["range"];

  // CHecking if the range/max/min values are available for the variable. If not then exit.
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

  // Printing the fxp version of the dictionary for the Uniform distribution.

  if(distribution == "UNIFORM_INT" || distribution == "UNIFORM_REAL"){
    
    if(c->symbolType(var) == "i1")
    	os << "(declare-fun "<< var << " () (_ SFXP 1 0))\n";

    // An integer variable is a signed fixed point with 0 bits for fraction part.
    else if(c->symbolType(var)[0] == 'i'){
      int width = stoi(c->symbolType(var).substr(1));
      os << "(set-info :domain \"" << var <<" UniformInt "<< min << " " << max <<"\")\n";
      os << "(declare-fun "<< var << " () (_ SFXP 32 0))\n";
    }

    else if(c->symbolType(var) == "float" || c->symbolType(var) == "double"){
      os << "(set-info :domain \"" << var <<" UniformReal "<< min <<" "<< max<<"\")\n";
      os << "(declare-fun "<< var << " () (_ SFXP 32 5))\n";
    }

    // else if(c->symbolType(var) == "double"){
    //   os << "(set-info :domain \"" << var <<" UniformReal "<< min <<" "<< max<<"\")\n";
    //   os << "(declare-fun "<< var << " () (_ SFXP 64 10))\n";
    // }

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
  indentLevel++;

  // For every symbol parse it in the dictionary
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

  // In case if no variable is present in the constraint, then there is no addition in the volume. So make the final assertion as a false statement such that it won't effect the volume.
  // In case if one of the variable is present then make a true assertion denoting that this constraint might help in counting the volume.
  if(no_var)
    os << " false ))\n";
  else
    os << " true ))\n";

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

  else if(element->getType()->getWidth() == 1 && element->getValue() == 0)      // BCONST(false)
    result = "false";

  else{
    std::string number = std::bitset<32>(int(element->getValue())).to_string();
    result = "((_ sfxp 0) #b" + number + ")";
  }

  visitResults.push_back(result);
}

void FXPPrinter::endVisit(FloatConstant * element) {

  const int precision = 5;

  std::string number = (std::bitset<32-precision>(int(element->getValue()))).to_string();
  std::string decimal = (std::bitset<precision>(int((element->getValue() - int(element->getValue())) * pow(2,precision)))).to_string();

  std::string result = "((_ sfxp " + std::to_string(precision) + ") #b" + number + decimal + ")"; 
  visitResults.push_back(result);
}

void FXPPrinter::endVisit(DoubleConstant * element) {

  const int precision = 5;

  std::string number = (std::bitset<32-precision>(int(element->getValue()))).to_string();
  std::string decimal = (std::bitset<precision>(int((element->getValue() - int(element->getValue())) * pow(2,precision)))).to_string();

  std::string result = "((_ sfxp " + std::to_string(precision) + ") #b" + number + decimal + ")"; 
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
  // std::string result_width = "128";

  // Get the operand
  std::string result1 = visitResults.back();
  visitResults.pop_back();

  // Get the operator
  std::string op = theConstraint->op2str(element->getOp());
  std::string result = "";

  // if(op == "sitofp" || op == "fptosi" || op == "sext" || op == "trunc" || op == "sin" || op == "cos" || op == "tan"){
  //   t = element->getConstraint()->type2str(element->getType());
  //   width = (t == "float" ? "32" : "64");
  // }

  if(mapping.find(op) != mapping.end())
    result += mapping[op];
  else{
    std::cerr << "\nUnary key not found..." << op <<"\n";
    return;
  }

  // if(op == "llvm.sin.f32" || op == "llvm.sin.f64" || op == "llvm.cos.f32" || op == "llvm.cos.f64" || op == "llvm.tan.f32" || op == "llvm.tan.f64")
  //   op = op.substr(5,3);


  // if(op.find("llvm.floor") != -1)
  //   result += "(> (fp.to_real " + result1 + ") 0) " + "(fp.roundToIntegral RTZ " + result1 + ") (fp.roundToIntegral RTN " + result1 + "))";
  // else if(op.find("llvm.ceil") != -1)
  //   result += "(> (fp.to_real " + result1 + ") 0) " + "(fp.roundToIntegral RTP " + result1 + ") (fp.roundToIntegral RTZ " + result1 + "))";
  // else if(op == "sitofp")
  //   result += "(= " + width + " 32) " + "((_ to_fp 8 24) " + result1 + ") " + "((_ to_fp 11 53) " + result1 + "))";
  // else if(op == "fptosi")
  //   result += "((_ fp.to_sbv " + width + ") RNE " + result1 + ")"; //"(= " + width + " 32) " + "( (_ fp.to_sbv 32) RNE " + result1 + ") ( (_ fp.to_sbv 64) RNE " + result1 + ")";
  
  // Making trunc as identity for now. 
  if(op == "trunc"){
    // width = (t.substr(1));
    t = element->getConstraint()->type2str(element->getType());

   	if(t == "i1")
   		result += "(sfxp.gt " + result1 + " ((_ sfxp 0) #x00000000))";

   	else
   		result += result1;
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

