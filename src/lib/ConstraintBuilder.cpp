#include "ConstraintBuilder.h"

#include <vector>
#include <cassert>

using namespace antlrcpp;

ConstraintBuilder::ConstraintBuilder(ConstraintGrammarParser *p) : parser{p} {}

static std::shared_ptr<Constraint::Expr> visitedExpr;
static std::shared_ptr<Constraint::Constraints> theConstraint;

std::shared_ptr<Constraint::Constraints>
ConstraintBuilder::build(ConstraintGrammarParser::ConstraintContext *ctx) {
  theConstraint = std::make_shared<Constraint::Constraints>();

  // Visit the dictionary entries and define them in theConstraint
  for (auto sd : ctx->symbolDef()) {
    visit(sd);
  }

  // Visit the expression
  visit(ctx->expr()); 
  theConstraint->setExpr(visitedExpr);

  return theConstraint;
}

Any ConstraintBuilder::visitSymbolDef(  //changed by SBH

  ConstraintGrammarParser::SymbolDefContext *ctx) {
  std::string name = ctx->IDENTIFIER()->getText();
  std::string type = ctx->TYPE()->getText();
  // std::string val = ctx->NUMBER()->getText();

//changed by Rishab

  // std::vector range_specs = ctx->rangeSpec()->NUMBER();
  // std::string min_range = "-100";//range_specs[0]->getText();
  // std::string max_range = "100";//range_specs[1]->getText();

//Added by Rishab to support Different Distributions
  // std::string dist_name;
  // std::string param1, param2;

  // dist_name = "uniform";
  // param1 = "0";
  // param2 = "0";

  theConstraint->defineSymbol(name, type);
  return "";
}

Any ConstraintBuilder::visitSymbolExpr(
      ConstraintGrammarParser::SymbolExprContext *ctx) {
  std::string name = ctx->IDENTIFIER()->getText();
  assert(theConstraint->isDefined(name) &&
         "Use of symbol that is not in the dictionary");
  visitedExpr = theConstraint->create(name, theConstraint->str2type(theConstraint->symbolType(name)));
  return "";
}

Any ConstraintBuilder::visitConstantExpr(ConstraintGrammarParser::ConstantExprContext *ctx) {
  auto type = theConstraint->str2type(ctx->TYPE()->getText());
  std::string val = ctx->NUMBER()->getText();
  if (type->getBase() == Constraint::Type::Base::Int) {
    switch (type->getWidth()) {
    case 1:
    case 8:
    case 16:
    case 32:
    case 64:
      visitedExpr = theConstraint->create(std::stol(val), type);
      break;
    default:
      assert(false && "Invalid width for Int Constraint::Type");
    } 
  } else {
    switch (type->getWidth()) {
    case 32:
      visitedExpr = theConstraint->create(std::stof(val), type);
      break;
    case 64:
      visitedExpr = theConstraint->create(std::stod(val), type);
      break;
    default:
      assert(false && "Invalid width for Float Constraint::Type");
    } 
  }
  return "";
}

Any ConstraintBuilder::visitUnaryExpr(ConstraintGrammarParser::UnaryExprContext *ctx) {
  auto op = theConstraint->str2op(ctx->UNOP()->getText());
  visit(ctx->expr());
  visitedExpr = theConstraint->create(visitedExpr, op);
  return "";
}

Any ConstraintBuilder::visitCastExpr(ConstraintGrammarParser::CastExprContext *ctx) {
  auto op = theConstraint->str2op(ctx->CASTOP()->getText());
  visit(ctx->expr());
  auto type = theConstraint->str2type(ctx->TYPE()->getText());
  visitedExpr = theConstraint->create(visitedExpr, op, type);
  return "";
}


Any ConstraintBuilder::visitBinaryExpr(ConstraintGrammarParser::BinaryExprContext *ctx) {
  auto op = theConstraint->str2op(ctx->BINOP()->getText());
  visit(ctx->expr(0));
  std::shared_ptr<Constraint::Expr> c1 = visitedExpr;
  visit(ctx->expr(1));

  visitedExpr = theConstraint->create(c1, visitedExpr, op);
  return "";
}


//added by SBH
Any ConstraintBuilder::visitUnIntrExpr(ConstraintGrammarParser::UnIntrExprContext *ctx) {
  auto op = theConstraint->str2op(ctx->UNINTRFUN()->getText());
  visit(ctx->expr());
  auto type = theConstraint->str2type(ctx->TYPE()->getText());
  visitedExpr = theConstraint->create(visitedExpr, op, type);

  return "";
}

//added by SBH
Any ConstraintBuilder::visitBinIntrExpr(ConstraintGrammarParser::BinIntrExprContext *ctx) {
  auto op = theConstraint->str2op(ctx->BININTRFUN()->getText());
  auto type = theConstraint->str2type(ctx->TYPE()->getText());

  // std::cout<<"OP:" << op<< "\nType: "<<type->getWidth()<<"\n";

  visit(ctx->expr(0));
  std::shared_ptr<Constraint::Expr> c1 = visitedExpr;
  visit(ctx->expr(1));
  visitedExpr = theConstraint->create(c1, visitedExpr, op, type);
  return "";
}

