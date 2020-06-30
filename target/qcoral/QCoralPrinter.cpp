#include "QCoralPrinter.h"
#include <iostream>

using namespace Constraint;

std::map<std::string, std::string> dictionary;
std::map<std::string, int> seen;							// For checking if the id occurs in constraint or not
int id = 1;
std::map<std::string, std::string> mapping = {

{"fneg", "MUL("},
{"fptosi", "ASINT("},

{"trunc", ""},				// Previously it was ASINT(
{"zext", ""},				// ""
{"sext", ""},				// ""
{"fptrunc", ""},			// Previously it was ASDOUBLE(
{"fpext", ""},				// ""

{"sitofp", "ASDOUBLE("},
{"add", "ADD("},
{"sub", "SUB("},
{"mul", "MUL("},
{"sdiv", "DIV("},
{"srem", "MOD("},
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
{"olt", "DLT("},
{"ole", "DLE("},
{"ogt", "DGT("},
{"oge", "DGE("},

// {"ult", "ILT("},
// {"fult", "DLT("},

{"land", "BAND("},
{"lor", "BOR("},
{"lnot", "BNOT("}
};

void QCoralPrinter::print(std::shared_ptr<Constraint::Constraint> c) {
  theConstraint = c;
  os << ":Variables:\n";
  indentLevel++;
  int num = c->symbols.size();
  for (auto &n : c->symbols) {
    num--;
    if(c->symbolType(n)[0] == 'i'){
      if(c->symbolType(n) == "i1")
        os << id << " UNIFORM_INT -1 1";
      else if(c->symbolType(n) == "i8")
        os << id << " UNIFORM_INT -129 127";
      else if(c->symbolType(n) == "i16")
        os << id << " UNIFORM_INT -32769 32767";
      else if(c->symbolType(n) == "i32")
        os << id << " UNIFORM_INT -999999999 999999999"; //Full range not working
      else if(c->symbolType(n) == "i64")
        os << id << " UNIFORM_INT -999999999 999999999";  // -9223372036854775809 9223372036854775807 (Full range not working)
      else{
        os << "Invalid Integer type. Exiting!!\n";
        return;
      }
      dictionary[n] = "IVAR(id_" + std::to_string(id)+")";
    }

    else if(c->symbolType(n) == "long"){
      os << id << " UNIFORM_INT -999999999 999999999";			// -1.17549e-38 3.4e+38 (Full range not working)
      dictionary[n] = "IVAR(id_" + std::to_string(id)+")";
    }

    else if(c->symbolType(n) == "float"){
      os << id << " UNIFORM_REAL -1.17549e-4 3.4e+4";			// -1.17549e-38 3.4e+38 (Full range not working)
      dictionary[n] = "DVAR(id_" + std::to_string(id)+")";
    }

    else if(c->symbolType(n) == "double"){
      os << id << " UNIFORM_REAL -2.22507e-4 1.7e+4";		// -2.22507e-308 1.7e+308 (Full Range not working)
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
  c->getExpr()->accept(this); 
  os << visitResults.back();
  visitResults.pop_back();
  for(auto it: seen){
  	if(it.second == 0){
  		if(it.first[0] == 'D')
  			os<<";DEQ("<<it.first<<","<<it.first<<")";
  		else
  			os<<";IEQ("<<it.first<<","<<it.first<<")";
  	}
  		
  }
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

  if(element->getType()->getWidth() == 1 && element->getValue() == 1)						// BCONST(true)
  	result = "IEQ(ICONST(1), ICONST(1))";

  else if(element->getType()->getWidth() == 1 && element->getValue() == 0)					// BCONST(false)
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
    result += "\nUnary key not found... Exiting!!\n";
    return;
  }

  if(op == "fneg")
    result += ", DCONST(-1)";
  
  if(result == ""){

  	if(op == "trunc" && theConstraint->type2str(element->getType()) == "i1"){
  		//os<<"\nResult1 --> "<<result1<<"\n";
  		if(result1 == "ICONST(0)" || result1 == "IEQ(ICONST(1), ICONST(0))")
  			result = "IEQ(ICONST(1), ICONST(0))";
  		else
  			result = "IEQ(ICONST(1), ICONST(1))";
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
    result += "\nBinary key not found... Exiting!!\n";
    return;
  }

  if(op == "trunc" || op == "zext" || op == "sext" || op == "fptrunc" || op == "fpext")
    result += result2 + ")";
  else
    result += result1 + "," + result2 + ")";
  visitResults.push_back(result);
}   									

std::string QCoralPrinter::indent() const {
  return std::string(indentLevel*indentSize, ' ');
}

