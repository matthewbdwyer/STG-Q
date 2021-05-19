#include "QCoralPrinter.h"
#include <jsoncpp/json/json.h>

using namespace Constraint;

/*
 * Globals for communicating the information between the functions.
*/

//! For checking if the variable occurs in the constraint or not.
std::map<std::string, int> seen;    

//! Qcoral requires id numbers instead of variable names. So, X -> id_1, Y -> id_2 etc.          
int id = 1;

//! Mapping from variable name to id numbers.
std::map<std::string, std::string> dictionary;

//! For checking if any variable is present in the constraint
bool no_var = true;

/*
 * Mapping from stg functions to qcoral functions.
*/ 

std::map<std::string, std::string> mapping = {

{"fneg", "MUL("},
{"fptosi", "ASINT("},

{"trunc", ""},       
{"zext", ""},       
{"sext", ""},       
{"fptrunc", ""},      
{"fpext", ""},        

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
{"fune", "DNE("}, 
{"olt", "DLT("},
{"ole", "DLE("},
{"ogt", "DGT("},
{"oge", "DGE("},
{"ult", ""},
{"ugt", ""},
{"fult", ""},
{"fugt", ""},
{"land", "BAND("},
{"lor", "BOR("},
{"lnot", "BNOT("},
{"xor", "BXOR("},

//Intrinsics UNARY

{"llvm.sin.f32", "SIN_("},
{"llvm.sin.f64", "SIN_("},
{"llvm.sin.f80", "SIN_("},
{"llvm.sin.f128", "SIN_("},

{"llvm.cos.f32", "COS_("},
{"llvm.cos.f64", "COS_("},
{"llvm.cos.f80", "COS_("},
{"llvm.cos.f128", "COS_("},

{"tan.f32", "TAN_("},

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

{"atan2.f32", "ATAN2_("},

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
{"llvm.maximum.f128", "MAX_("},

{"sin","SIN_("},
{"cos","COS_("},
{"tan","TAN_("},
{"atan2", "ATAN2_("},
{"log","LOG_("},
{"log10f","LOG10_("},
{"sqrt","SQRT_("},
{"pow","POW_("},
{"exp","EXP_("},
{"expf","EXP_("}

};


//! Function for parsing dictionary for a specific variable.
void QCoralPrinter::parseDict(const char *dict, std::string var, std::string type) {

  Json::Value root;
  std::ifstream ifs;
  ifs.open(std::string(dict));
  ifs >> root;

  Json::Value data = root[var];

  // Checking if data for the variable is available in the dictionary. If not then exit.
  if(data.isNull()){
    throw ("No data available for: " + var);
  }

  std::string distribution = data["distribution"].asString();
  
  // Checking if the distribution data is available for the variable. If not then default to Uniform Distribution.
  if(distribution.empty()){
    if(type == "float" || type == "double"){
      std::cerr<<"No distribution set for: "<< var <<". Setting default distribution (UNIFORM_REAL)"<<"\n";
      distribution = "UNIFORM_REAL";
    }

    else{
      std::cerr<<"No distribution set for: "<< var <<". Setting default distribution (UNIFORM_INT)"<<"\n";
      distribution = "UNIFORM_INT";
    }
  }

  Json::Value range = data["range"];
  std::string max, min;

  // CHecking if the range data is available for the variable. If not then default to ranges defined by the type.
  if(range.isNull()){
    if(type == "float" || type == "double"){
      std::cerr<<"No Range available for: "<< var<<". Setting default range (-1,000,000 to 1,000,000)\n";
      min = "-1000000";
      max = "1000000";
    }

    else if(type == "i8"){
      std::cerr<<"No Range available for: "<< var<<". Setting default range (-128 to 127)\n";
      min = "-128";
      max = "127";
    }

    else if(type == "i16"){
      std::cerr<<"No Range available for: "<< var<<". Setting default range (-32,768 to 32,767)\n";
      min = "-32768";
      max = "32767";
    }

    else if(type == "i32"){
      std::cerr<<"No Range available for: "<< var<<". Setting default range (-1,000,000 to 1,000,000)\n";
      min = "-1000000";
      max = "1000000";
    }

    else if(type == "i64" || type == "long"){
      std::cerr<<"No Range available for: "<< var<<". Setting default range (-1,000,000 to 1,000,000)\n";
      min = "-1000000";
      max = "1000000";
    }

    else{
      throw ("\n This should never happen.. Invalid data type!! "+ var + "\n");
    }
  }

  else{

    max = range["max"].asString();

    if(max.empty()){
      throw ("No Max value available for: " + var);
    }

    min = range["min"].asString();

    if(min.empty()){
      throw ("No min value available for: " + var);
    }

  }

  // Printing the Qcoral version of the dictionary depending on the distribution.

  if(distribution == "UNIFORM_INT" || distribution == "UNIFORM_REAL")
    os<<id<<" "<< distribution<< " "<< min << " "<< max<< "\n";

  else{
    Json::Value parameters = data["parameters"];

    if(distribution == "GEOMETRIC"){
      std::string p = parameters["p"].asString();
      if(p.empty()){
        throw ("No probability given for: " + var + "\n");
      }
      os<<id<<" "<< distribution<< " "<< min << " "<< max<< " "<< p<<"\n";
    }

    else if(distribution == "POISSON"){
      std::string lambda = parameters["lambda"].asString();
      if(lambda.empty()){
        throw ("No lambda given for: " + var + "\n");
      }
      os<<id<<" "<< distribution<< " "<< min << " "<< max<< " "<< lambda<<"\n";
    }

    else if(distribution == "EXPONENTIAL"){
      std::string mean = parameters["mean"].asString();
      if(mean.empty()){
        throw ("No mean given for: " + var + "\n");
      }
      os<<id<<" "<< distribution<< " "<< min << " "<< max<< " "<< mean<<"\n";
    }

    else if(distribution == "BINOMIAL"){
      std::string num_trials = parameters["num_trials"].asString();
      std::string p = parameters["p"].asString();

      if(num_trials.empty() || p.empty()){
        throw ("Insufficient parameters given for: " + var + ". A binomial variable requires num_trials and probability.\n");
      }
      os<<id<<" "<< distribution<< " "<< min << " "<< max<< " "<< num_trials<<" "<<p<<"\n";
    }

    else if(distribution == "NORMAL"){
      std::string mean = parameters["mean"].asString();
      std::string sd = parameters["sd"].asString();

      if(mean.empty() || sd.empty()){
        throw ("Insufficient parameters given for: " + var + ". A normal variable requires mean and standard deviation.\n");
      }
      os<<id<<" "<< distribution<< " "<< min << " "<< max<< " "<< mean<<" "<<sd<<"\n";
    }

    else{
      throw ("Invalid distribution for: " + var + "\n");
    }
  }

}


void QCoralPrinter::print(std::shared_ptr<Constraint::Constraints> c, const char *dict) {
  
  theConstraint = c;
  no_var = true; 
  // Initially printing the dictionary
  os << ":Variables:\n";
  indentLevel++;

  int num = c->symbols.size();

  try{

    for (auto &n : c->symbols) {
      num--;

      // If dictionary is given then parse the dictionary else default everything to Uniform distribution and appropriate ranges governed by the type.
      if(dict != NULL)
        parseDict(dict, n, c->symbolType(n));

      else{

        std::string distribution, max, min;

        if(c->symbolType(n) == "float" || c->symbolType(n) == "double"){
          std::cerr<<"No distribution set for: "<< n <<". Setting default distribution (UNIFORM_REAL)"<<"\n";
          distribution = "UNIFORM_REAL";
          std::cerr<<"No Range available for: "<< n <<". Setting default range (-1,000,000 to 1,000,000)\n";
          min = "-1000000";
          max = "1000000";
        }

        else{
          std::cerr<<"No distribution set for: "<< n <<". Setting default distribution (UNIFORM_INT)"<<"\n";
          distribution = "UNIFORM_INT";
        }

        if(c->symbolType(n) == "i8"){
          os << ";; No Range available for: "<< n<<". Setting default range (-128 to 127)\n";
          min = "-128";
          max = "127";
        }

        else if(c->symbolType(n) == "i16"){
          os << ";; No Range available for: "<< n <<". Setting default range (-32,768 to 32,767)\n";
          std::cerr<<"No Range available for: "<< n <<". Setting default range (-32,768 to 32,767)\n";
          min = "-32768";
          max = "32767";
        }

        else if(c->symbolType(n) == "i32"){
          os << ";; No Range available for: "<< n<<". Setting default range (-1,000,000 to 1,000,000)\n";
          std::cerr<<"No Range available for: "<< n<<". Setting default range (-1,000,000 to 1,000,000)\n";
          min = "-1000000";
          max = "1000000";
        }

        else if(c->symbolType(n) == "i64" || c->symbolType(n) == "long"){
          os << ";; No Range available for: "<< n<<". Setting default range (-1,000,000 to 1,000,000)\n";
          std::cerr<<"No Range available for: "<< n<<". Setting default range (-1,000,000 to 1,000,000)\n";
          min = "-1000000";
          max = "1000000";
        }

        else if(c->symbolType(n) != "float" && c->symbolType(n) != "double"){
          throw ("\n This should never happen. Invalid data type!! " + n + "\n");
        }

        os<<id<<" "<< distribution<< " "<< min << " "<< max<< "\n";

      }

      // Now saving variables in a dictionary for fast lookup
      if(c->symbolType(n)[0] == 'i'){
        if(c->symbolType(n) == "i1" || c->symbolType(n) == "i8" || c->symbolType(n) == "i16" || c->symbolType(n) == "i32" || c->symbolType(n) == "i64" || c->symbolType(n) == "long"){
          dictionary[n] = "IVAR(id_" + std::to_string(id)+")";
        }
        else{
          throw ("This should never happen. Invalid Integer type!!\n");
        }
      }

      else if(c->symbolType(n) == "float" || c->symbolType(n) == "double"){
        dictionary[n] = "DVAR(id_" + std::to_string(id)+")";
      }

      else{
        throw ("This should never happen. Invalid data type.\n");
      }

      // Initially setting variable is not seen 
      seen[dictionary[n]] = 0;
      id++;
    }

    indentLevel--;
    os << "\n";

    os << ":Constraints:\n";
    os << "BAND(";


    // For every variable in seen make a trivial equality that the variable equals itself.
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

    // In case if no variable is present in the constraint, then there is no addition in the volume. So make the final assertion as a false statement such that it won't effect the volume.
    // In case if one of the variable is present then make a true assertion denoting that this constraint might help in counting the volume.
    if(no_var)
      os<<", IEQ(ICONST(1), ICONST(0)))";
    else
      os<<", IEQ(ICONST(1), ICONST(1)))";

  }

  catch(std::string s){
    os << "Error: "<< s <<"\n";
    std::cerr << "QCoralPrinter Error: "<< s <<"\n";
  }

  os << "\n";
  os.flush();
}

void QCoralPrinter::endVisit(Symbol * element) {
  if(dictionary.find(element->getName()) != dictionary.end()){
    std::string name = dictionary[element->getName()];
    //int id_no = stoi(name.substr(8, name.length()-9));
    seen[name] = 1;
    no_var = false;
    visitResults.push_back(name);
  }
  else
    throw ("\nThis should never happen. ELEMENT NOT FOUND IN DICTIONARY --> " + element->getName() + "\n");
}

void QCoralPrinter::endVisit(IntConstant * element) {
  
  std::string result;

  if(element->getType()->getWidth() == 1 && element->getValue() == 1)           // BCONST(true)
    result = "IEQ(ICONST(1), ICONST(1))";

  else if(element->getType()->getWidth() == 1 && element->getValue() == 0)       // BCONST(false)
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

  // Getting the input to the unary expression
  std::string result1 = visitResults.back();
  visitResults.pop_back();

  // Getting the unary operator
  std::string op = theConstraint->op2str(element->getOp());
  std::string result = "";

  // Check if the mapping is present
  if(mapping.find(op) != mapping.end())
    result += mapping[op];
  else{
    throw ("\n This should never happen. Unary key not found..." + op);
  }


  // Conversion for fneg. Multiplying by -1.
  if(op == "fneg")
    result += result1 + ", DCONST(-1))";

  // ceil, floor and abs are not supported.
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
  
  else if(result == ""){

    // Conversion for truncating to bools. Only constant value can be supported and nothing else.
    if(op == "trunc" && theConstraint->type2str(element->getType()) == "i1"){
      if(result1 == "ICONST(0)" || result1 == "IEQ(ICONST(1), ICONST(0))")
        result = "IEQ(ICONST(1), ICONST(0))";
      else if (result1 == "ICONST(1)" || result1 == "IEQ(ICONST(1), ICONST(1))")
        result = "IEQ(ICONST(1), ICONST(1))";
      else{
        throw ("\n Trunc operation on " + result1 + " is not supported \n");
      }
    }

    // Conversion for extending of integers. Only constant booleans can be extended.
    else if(op == "zext" && theConstraint->type2str(element->getType())[0] == 'i'){
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

  // Getting the operands
  std::string result2 = visitResults.back();
  visitResults.pop_back();
  std::string result1 = visitResults.back();
  visitResults.pop_back();

  // Getting the operator
  std::string op = theConstraint->op2str(element->getOp());
  std::string result = "";

  if( mapping.find(op) != mapping.end())
    result += mapping[op];
  else{
    throw ("\n This should never happen. Binary key not found..." + op);
  }

  // if(op == "trunc" || op == "zext" || op == "sext" || op == "fptrunc" || op == "fpext"){
  //   std::cerr<<" zext came here trunc, zext, sext, fptrunc & fpext in binary expression. This should not happen\n";
  //   result += result2 + ")";
  // }


  // Conversion for unsigned less than/greater than for floats and ints
  if(op == "ult")
    result += "BOR(BAND(IGE("+result1+", ICONST(0)), BAND(IGE("+result2+", ICONST(0)), ILT("+result1+", "+result2+"))),\
      BOR(BAND(ILT("+result1+", ICONST(0)), BAND(ILT("+result2+", ICONST(0)), IGT("+result1+", "+result2+"))),\
        BOR(BAND(IGE("+result1+", ICONST(0)), BAND(ILT("+result2+", ICONST(0)), ILT("+result1+", MUL("+result2+", ICONST(-1))))),\
        BAND(ILT("+result1+", ICONST(0)), BAND(IGE("+result2+", ICONST(0)), ILT(MUL("+result1+", ICONST(-1)), "+result2+"))))))";

  else if(op == "fult")
      result += "BOR(BAND(DGE("+result1+", DCONST(0)), BAND(DGE("+result2+", DCONST(0)), DLT("+result1+", "+result2+"))),\
      BOR(BAND(DLT("+result1+", DCONST(0)), BAND(DLT("+result2+", DCONST(0)), DGT("+result1+", "+result2+"))),\
        BOR(BAND(DGE("+result1+", DCONST(0)), BAND(DLT("+result2+", DCONST(0)), DLT("+result1+", MUL("+result2+", DCONST(-1))))),\
        BAND(DLT("+result1+", DCONST(0)), BAND(DGE("+result2+", DCONST(0)), DLT(MUL("+result1+", DCONST(-1)), "+result2+"))))))";

  else if(op == "ugt")
    result += "BOR(BAND(IGE("+result1+", ICONST(0)), BAND(IGE("+result2+", ICONST(0)), IGT("+result1+", "+result2+"))),\
      BOR(BAND(ILT("+result1+", ICONST(0)), BAND(ILT("+result2+", ICONST(0)), ILT("+result1+", "+result2+"))),\
        BOR(BAND(IGE("+result1+", ICONST(0)), BAND(ILT("+result2+", ICONST(0)), IGT("+result1+", MUL("+result2+", ICONST(-1))))),\
        BAND(ILT("+result1+", ICONST(0)), BAND(IGE("+result2+", ICONST(0)), IGT(MUL("+result1+", ICONST(-1)), "+result2+"))))))";
  
  else if(op == "fugt")
      result += "BOR(BAND(DGE("+result1+", DCONST(0)), BAND(DGE("+result2+", DCONST(0)), DGT("+result1+", "+result2+"))),\
      BOR(BAND(DLT("+result1+", DCONST(0)), BAND(DLT("+result2+", DCONST(0)), DLT("+result1+", "+result2+"))),\
        BOR(BAND(DGE("+result1+", DCONST(0)), BAND(DLT("+result2+", DCONST(0)), DGT("+result1+", MUL("+result2+", DCONST(-1))))),\
        BAND(DLT("+result1+", DCONST(0)), BAND(DGE("+result2+", DCONST(0)), DGT(MUL("+result1+", DCONST(-1)), "+result2+"))))))"; 

  // Conversion for signed remainder division. For more info look at the mapping for srem.
  else if(op == "srem")
  	result += "ASDOUBLE(" + result1 + "), " + "ASDOUBLE(" + result2 + ")))";

  else
    result += result1 + "," + result2 + ")";
  visitResults.push_back(result);
}                     

std::string QCoralPrinter::indent() const {
  return std::string(indentLevel*indentSize, ' ');
}

