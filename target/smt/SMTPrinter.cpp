#include "SMTPrinter.h"
#include <iostream>

using namespace Constraint;

std::map<std::string, std::string> dictionary;
int id = 1;
std::map<std::string, std::string> mapping = {

{"fneg", ""},
{"fptosi", "(to_int"},

{"trunc", ""},        // Previously it was ASINT(
{"zext", ""},       // ""
{"sext", ""},       // ""
{"fptrunc", ""},      // Previously it was ASDOUBLE(
{"fpext", ""},        // ""

{"sitofp", "(to_real"},
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
{"ne", "(!= "},
{"slt", "(< "},
{"sle", "(<= "},
{"sgt", "(> "},
{"sge", "(>= "},
{"oeq", "(= "},
{"one", "(!= "},
{"fune", "(!= "},      // Newly added
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
{"llvm.sin.f80", "(sin "},
{"llvm.sin.f128", "(sin "},

{"llvm.cos.f32", "(cos "},
{"llvm.cos.f64", "(cos "},
{"llvm.cos.f80", "(cos "},
{"llvm.cos.f128", "(cos "},

{"llvm.exp.f32", "(pow EXP "},
{"llvm.exp.f64", "(pow EXP "},
{"llvm.exp.f80", "(pow EXP "},
{"llvm.exp.f128", "(pow EXP "},

{"llvm.log.f32", "(log "},
{"llvm.log.f64", "(log "},
{"llvm.log.f80", "(log "},
{"llvm.log.f128", "(log "},

{"llvm.log10.f32", "(log10 "},
{"llvm.log10.f64", "(log10 "},
{"llvm.log10.f80", "(log10 "},
{"llvm.log10.f128", "(log10 "},

{"llvm.sqrt.f32", "(sqrt "},
{"llvm.sqrt.f64", "(sqrt "},
{"llvm.sqrt.f80", "(sqrt "},
{"llvm.sqrt.f128", "(sqrt "},

{"llvm.exp2.f32", "(pow 2.0 "},
{"llvm.exp2.f64", "(pow 2.0 "},
{"llvm.exp2.f80", "(pow 2.0 "},
{"llvm.exp2.f128", "(pow 2.0 "},

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

{"llvm.pow.f32", "(pow "},
{"llvm.pow.f64", "(pow "},
{"llvm.pow.f80", "(pow "},
{"llvm.pow.f128", "(pow "},

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

void SMTPrinter::print(std::shared_ptr<Constraint::Constraints> c) {
  theConstraint = c;
  // os << "(set-option :print-success false)\n";
  // mvn package assembly:single
  // os << "(set-logic AUFLIRA)\n";
  // os << "(set-option :seed 121314)\n(set-option :partitioning true)\n(set-option :non-linear-counter \"qcoral\")\n";
  os << "(declare-const EXP Real)\n(assert (= EXP 2.71828182846))";

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

    // Initially getting the distribution and making the SMT dictionary

    if(distribution == "uniform" && c->symbolType(n) == "i1")
      os << "(declare-const id_"<< id << " Bool)";

    else if(distribution == "uniform" && c->symbolType(n)[0] == 'i'){
      os << "(declare-const id_"<< id << " Int)\n";
      os << "(assert (>= id_"<<id<<" "+ low <<" ))";
      os << "(assert (<= id_"<<id<<" "+ high <<" ))";
      // os << "(declare-var id_"<< id << " (Int "<< low << " " << high << "))";
    }

    else if(distribution == "uniform" && (c->symbolType(n) == "float" || c->symbolType(n) == "double")){
      os << "(declare-const id_"<< id << " Real)\n";
      os << "(assert (>= id_"<<id<<" "+ low <<" ))";
      os << "(assert (<= id_"<<id<<" "+ high <<" ))";
      // os << "(declare-var id_"<< id << " (Float "<< low << " " << high << "))";    
    }

    else{
      std::cerr<<"Invalid TYPE!!  --> " << c->symbolType(n);
      exit(0);
    }

    dictionary[n] = "id_" + std::to_string(id);
    os << "\n";
    id++;
  }

  indentLevel--;
  os << "\n";

  os << "(assert ";

  c->getExpr()->accept(this); 
  os << visitResults.back();
  visitResults.pop_back();

  os << ")\n";
  os.flush();
}

void SMTPrinter::endVisit(Symbol * element) {
  if(dictionary.find(element->getName()) != dictionary.end()){
    std::string name = dictionary[element->getName()];
    //int id_no = stoi(name.substr(8, name.length()-9));
    // seen[name] = 1;
    visitResults.push_back(name);
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

  // else if(op.find("llvm.ceil") != std::string::npos){
  // 	// result = "BOR(BAND(DGT(" + result1 + ", DCONST(0)), DGT(ASDOUBLE(ASINT(ADD(" + result1 + ", DCONST(0.9999999999999)"
  // 	result += "ASINT(ADD(" + result1 + ", MUL(ASDOUBLE(DGT(" + result1 + ", DCONST(0))), DCONST(0.9999999999999)))))";
  // }

  // else if(op.find("llvm.floor") != std::string::npos){
  // 	result += "ASINT(SUB(" + result1 + ", MUL(ASDOUBLE(DLT(" + result1+ ", DCONST(0))), DCONST(0.9999999999999)))))";
  // }

  // else if(op.find("llvm.fabs") != std::string::npos){
  // 	result += "MUL(" + result1 + ", MUL(ASDOUBLE(DLT(" + result1 + ", DCONST(0.0))) , DCONST(-1.0))), MUL(" + result1 + ", ASDOUBLE(DGT(" + result1 + ", DCONST(0.0)))))";
  // }
  
  // else if(result == ""){

  //   if(op == "trunc" && theConstraint->type2str(element->getType()) == "i1"){
  //     //os<<"\nResult1 --> "<<result1<<"\n";
  //     if(result1 == "ICONST(0)" || result1 == "IEQ(ICONST(1), ICONST(0))")
  //       result = "IEQ(ICONST(1), ICONST(0))";
  //     else
  //       result = "IEQ(ICONST(1), ICONST(1))";
  //   }

  //   else if(op == "zext" && theConstraint->type2str(element->getType())[0] == 'i'){
  //     std::cerr<<"FOund zext...\t"<<result1<<"\n";
  //     if(result1 == "ICONST(0)" || result1 == "IEQ(ICONST(1), ICONST(0))")
  //       result = "ICONST(0)";
  //     else if(result1 == "ICONST(1)" || result1 == "IEQ(ICONST(1), ICONST(1))")
  //       result = "ICONST(1)";
  //     else
  //       result = "ASINT(" + result1 + ")";
  //   }

  //   else
  //   result = result1;
  // }

  else
    result += result1 + ")";

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

  else
  	result += result1 + " " + result2 + ")";

  visitResults.push_back(result);
}                     

std::string SMTPrinter::indent() const {
  return std::string(indentLevel*indentSize, ' ');
}

