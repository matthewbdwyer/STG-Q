#include "QCoralPrinter.h"
#include <iostream>

using namespace Constraint;

std::map<std::string, std::string> dictionary;
std::map<std::string, int> seen;              // For checking if the id occurs in constraint or not
int id = 1;
std::map<std::string, std::string> mapping = {

{"fneg", "MUL("},
{"fptosi", "ASINT("},

{"trunc", ""},        // Previously it was ASINT(
{"zext", ""},       // ""
{"sext", ""},       // ""
{"fptrunc", ""},      // Previously it was ASDOUBLE(
{"fpext", ""},        // ""

{"sitofp", "ASDOUBLE("},
{"add", "ADD("},
{"sub", "SUB("},
{"mul", "MUL("},
{"sdiv", "DIV("},
{"srem", "ASINT(MOD("},
{"fadd", "ADD("},
{"fsub", "SUB("},
{"fmul", "MUL("},
{"fdiv", "DIV("},
{"frem", "MOD("},

{"eq", "IEQ("},
{"ne", "INE("},
{"slt", "ILT("},
{"sle", "ILE("},
{"sgt", "IGT("},
{"sge", "IGE("},
{"oeq", "DEQ("},
{"one", "DNE("},
{"fune", "DNE("},      // Newly added
{"olt", "DLT("},
{"ole", "DLE("},
{"ogt", "DGT("},
{"oge", "DGE("},

// {"ult", "ILT("},
// {"fult", "DLT("},

{"land", "BAND("},
{"lor", "BOR("},
{"lnot", "BNOT("},

//Intrinsics UNARY

{"llvm.sin.f32", "SIN_("},
{"llvm.sin.f64", "SIN_("},
{"llvm.sin.f80", "SIN_("},
{"llvm.sin.f128", "SIN_("},

{"llvm.cos.f32", "COS_("},
{"llvm.cos.f64", "COS_("},
{"llvm.cos.f80", "COS_("},
{"llvm.cos.f128", "COS_("},

{"llvm.exp.f32", "EXP_("},
{"llvm.exp.f64", "EXP_("},
{"llvm.exp.f80", "EXP_("},
{"llvm.exp.f128", "EXP_("},

{"llvm.log.f32", "LOG_("},
{"llvm.log.f64", "LOG_("},
{"llvm.log.f80", "LOG_("},
{"llvm.log.f128", "LOG_("},

{"llvm.log10.f32", "LOG10_("},
{"llvm.log10.f64", "LOG10_("},
{"llvm.log10.f80", "LOG10_("},
{"llvm.log10.f128", "LOG10_("},

{"llvm.sqrt.f32", "SQRT_("},
{"llvm.sqrt.f64", "SQRT_("},
{"llvm.sqrt.f80", "SQRT_("},
{"llvm.sqrt.f128", "SQRT_("},

{"llvm.exp2.f32", "POW_(DCONST(2.0),"},
{"llvm.exp2.f64", "POW_(DCONST(2.0),"},
{"llvm.exp2.f80", "POW_(DCONST(2.0),"},
{"llvm.exp2.f128", "POW_(DCONST(2.0),"},

//New functions added for testing

{"llvm.floor.f32", "ASDOUBLE("},
{"llvm.floor.f64", "ASDOUBLE("},
{"llvm.floor.f80", "ASDOUBLE("},
{"llvm.floor.f128", "ASDOUBLE("},

{"llvm.ceil.f32", "ASDOUBLE("},
{"llvm.ceil.f64", "ASDOUBLE("},
{"llvm.ceil.f80", "ASDOUBLE("},
{"llvm.ceil.f128", "ASDOUBLE("},

{"llvm.fabs.f32", "ADD("},
{"llvm.fabs.f64", "ADD("},
{"llvm.fabs.f80", "ADD("},
{"llvm.fabs.f128", "ADD("},

//Intrinsics BINARY

{"llvm.pow.f32", "POW_("},
{"llvm.pow.f64", "POW_("},
{"llvm.pow.f80", "POW_("},
{"llvm.pow.f128", "POW_("},

{"llvm.minnum.f32", "MIN_("},
{"llvm.minnum.f64", "MIN_("},
{"llvm.minnum.f80", "MIN_("},
{"llvm.minnum.f128", "MIN_("},

{"llvm.maxnum.f32", "MAX_("},
{"llvm.maxnum.f64", "MAX_("},
{"llvm.maxnum.f80", "MAX_("},
{"llvm.maxnum.f128", "MAX_("},

{"llvm.minimum.f32", "MIN_("},
{"llvm.minimum.f64", "MIN_("},
{"llvm.minimum.f80", "MIN_("},
{"llvm.minimum.f128", "MIN_("},

{"llvm.maximum.f32", "MAX_("},
{"llvm.maximum.f64", "MAX_("},
{"llvm.maximum.f80", "MAX_("},
{"llvm.maximum.f128", "MAX_("}

};

void QCoralPrinter::print(std::shared_ptr<Constraint::Constraints> c) {
  theConstraint = c;
  os << ":Variables:\n";
  indentLevel++;
  int num = c->symbols.size();
  for (auto &n : c->symbols) {
    num--;
    std::string low, high;
    std::string ranges = c->symbolRange(n);     // Can be changed if symbolRange returns a pair instead of a string
    int ind = ranges.find(" ");
    low = ranges.substr(0, ind);
    high = ranges.substr(ind+1);

    //Added to support distributions
    std::string distribution = c->get_distribution(n);
    std::pair<std::string, std::string> params = c->get_params(n);

    // Initially getting the distribution and making the qcoral dictionary

    if(distribution == "uniform" && c->symbolType(n)[0] == 'i')
        os << id << " UNIFORM_INT "<<low<<" "<<high;

    else if(distribution == "uniform")
        os << id << " UNIFORM_REAL "<<low<<" "<<high;
        
    else if(distribution == "exponential")
      os<< id << " EXPONENTIAL "<<low<<" "<<high<<" "<< params.first;

    else if(distribution == "binomial")
      os<< id << " BINOMIAL "<<low<<" "<<high<<" "<< params.first << " "<< params.second;

    else if(distribution == "poisson")
      os<< id << " POISSON "<<low<<" "<<high<<" "<< params.first;

    else if(distribution == "geometric")
      os<< id << " GEOMETRIC "<<low<<" "<<high<<" "<< params.first;

    else if(distribution == "normal")
      os<< id << " NORMAL "<<low<<" "<<high<<" "<< params.first << " "<< params.second;

    else{
      std::cerr<<"Invalid distribution!!";
      exit(0);
    }

    // Now saving variables in a dictionary for lookup

    if(c->symbolType(n)[0] == 'i'){
      if(c->symbolType(n) == "i1" || c->symbolType(n) == "i8" || c->symbolType(n) == "i16" || c->symbolType(n) == "i32" || c->symbolType(n) == "i64" || c->symbolType(n) == "long"){
        dictionary[n] = "IVAR(id_" + std::to_string(id)+")";
      }
      else{
        os << "Invalid Integer type. Exiting!!\n";
        exit(0);
      }
    }

    else if(c->symbolType(n) == "float" || c->symbolType(n) == "double"){
      dictionary[n] = "DVAR(id_" + std::to_string(id)+")";
    }

    else{
      os << "Invalid data type. Exiting!!\n";
      return;
    }

    //os << "(" << c->symbolType(n)[0] << ")" << " = " << c->symbolValue(n);
    os << "\n";
    seen[dictionary[n]] = 0;
    id++;
  }

  indentLevel--;
  os << "\n";

  os << ":Constraints:\n";
  
  for(auto it: seen){
    if(it.second == 0){
      if(it.first[0] == 'D')
        os<<"BAND(DEQ("<<it.first<<","<<it.first<<"), ";
      else
        os<<"BAND(IEQ("<<it.first<<","<<it.first<<"), ";
    }    
  }

  c->getExpr()->accept(this); 
  os << visitResults.back();
  visitResults.pop_back();

  for(auto it: seen)
    os<<")";

  os << "\n";
  os.flush();
}

void QCoralPrinter::endVisit(Symbol * element) {
  if(dictionary.find(element->getName()) != dictionary.end()){
    std::string name = dictionary[element->getName()];
    //int id_no = stoi(name.substr(8, name.length()-9));
    seen[name] = 1;
    visitResults.push_back(name);
  }
  else
    visitResults.push_back("\nELEMENT NOT FOUND IN DICTIONARY --> " + element->getName() + "\n");
}

void QCoralPrinter::endVisit(IntConstant * element) {
  
  std::string result;

  if(element->getType()->getWidth() == 1 && element->getValue() == 1)           // BCONST(true)
    result = "IEQ(ICONST(1), ICONST(1))";

  else if(element->getType()->getWidth() == 1 && element->getValue() == 0)          // BCONST(false)
    result = "IEQ(ICONST(1), ICONST(0))";

  else
    result = "ICONST(" + std::to_string(element->getValue()) + ")"; 

  visitResults.push_back(result);
}

void QCoralPrinter::endVisit(FloatConstant * element) {

  std::string result = "DCONST(" + std::to_string(element->getValue()) + ")"; 
  visitResults.push_back(result);
}

void QCoralPrinter::endVisit(DoubleConstant * element) {

  std::string result = "DCONST(" + std::to_string(element->getValue()) + ")"; 
  visitResults.push_back(result);
}

bool QCoralPrinter::visit(UnaryExpr * element) {
  indentLevel++;
  return true;
}

void QCoralPrinter::endVisit(UnaryExpr * element) {
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
    result += result1 + ", DCONST(-1))";

  else if(op.find("llvm.ceil") != std::string::npos){
  	// result = "BOR(BAND(DGT(" + result1 + ", DCONST(0)), DGT(ASDOUBLE(ASINT(ADD(" + result1 + ", DCONST(0.9999999999999)"
  	result += "ASINT(ADD(" + result1 + ", MUL(ASDOUBLE(DGT(" + result1 + ", DCONST(0))), DCONST(0.9999999999999)))))";
  }

  else if(op.find("llvm.floor") != std::string::npos){
  	result += "ASINT(SUB(" + result1 + ", MUL(ASDOUBLE(DLT(" + result1+ ", DCONST(0))), DCONST(0.9999999999999)))))";
  }

  else if(op.find("llvm.fabs") != std::string::npos){
  	result += "MUL(" + result1 + ", MUL(ASDOUBLE(DLT(" + result1 + ", DCONST(0.0))) , DCONST(-1.0))), MUL(" + result1 + ", ASDOUBLE(DGT(" + result1 + ", DCONST(0.0)))))";
  }
  
  else if(result == ""){

    if(op == "trunc" && theConstraint->type2str(element->getType()) == "i1"){
      //os<<"\nResult1 --> "<<result1<<"\n";
      if(result1 == "ICONST(0)" || result1 == "IEQ(ICONST(1), ICONST(0))")
        result = "IEQ(ICONST(1), ICONST(0))";
      else
        result = "IEQ(ICONST(1), ICONST(1))";
    }

    else if(op == "zext" && theConstraint->type2str(element->getType()) == "i32"){
      // std::cerr<<"FOund zext...\t"<<result1<<"\n";
      if(result1 == "ICONST(0)" || result1 == "IEQ(ICONST(1), ICONST(0))")
        result = "ICONST(0)";
      else if(result1 == "ICONST(1)" || result1 == "IEQ(ICONST(1), ICONST(1))")
        result = "ICONST(1)";
      else
        result = "ASINT(" + result1 + ")";
    }

    else
    result = result1;
  }

  else
    result += result1 + ")";

  visitResults.push_back(result);
}       

bool QCoralPrinter::visit(BinaryExpr * element) {
  indentLevel++;
  return true;
}

void QCoralPrinter::endVisit(BinaryExpr * element) {

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
    // result += "\nBinary key not found... Exiting!!\n";
    return;
  }

  if(op == "trunc" || op == "zext" || op == "sext" || op == "fptrunc" || op == "fpext"){
    std::cerr<<" zext came here trunc, zext, sext, fptrunc & fpext in binary expression. This should not happen\n";
    result += result2 + ")";
  }

  else if(op == "srem")
  	result += "ASDOUBLE(" + result1 + "), " + "ASDOUBLE(" + result2 + ")))";

  else
    result += result1 + "," + result2 + ")";
  visitResults.push_back(result);
}                     

std::string QCoralPrinter::indent() const {
  return std::string(indentLevel*indentSize, ' ');
}
