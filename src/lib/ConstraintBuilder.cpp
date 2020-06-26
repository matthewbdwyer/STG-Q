#include "ConstraintBuilder.h"

#include <vector>
#include <cassert>

using namespace antlrcpp;

using namespace Constraint;

ConstraintBuilder::ConstraintBuilder(ConstraintGrammarParser *p) : parser{p} {}

static std::shared_ptr<Constraint::Expr> visitedExpr;
static std::shared_ptr<Constraint::Constraint> theConstraint;

std::shared_ptr<Constraint::Constraint>
ConstraintBuilder::build(ConstraintGrammarParser::ConstraintContext *ctx) {
  theConstraint = std::make_shared<Constraint::Constraint>();

  // Visit the dictionary entries and define them in theConstraint
  for (auto sd : ctx->symbolDef()) {
    visit(sd);
  }

  // Visit the expression
  visit(ctx->expr());	
  theConstraint->setExpr(visitedExpr);

  return theConstraint;
}

Any ConstraintBuilder::visitSymbolDef(
      ConstraintGrammarParser::SymbolDefContext *ctx) {
  std::string name = ctx->IDENTIFIER()->getText();
  std::string type = ctx->TYPE()->getText();
  std::string val = ctx->NUMBER()->getText();
  theConstraint->defineSymbol(name, type, val);
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
      visitedExpr = theConstraint->create(std::stoi(val), type);
      break;
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
  std::shared_ptr<Expr> c1 = visitedExpr;
  visit(ctx->expr(1));
  visitedExpr = theConstraint->create(c1, visitedExpr, op);
  return "";
}