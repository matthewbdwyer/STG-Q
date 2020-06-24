#pragma once

#include "ConstraintGrammarBaseVisitor.h"
#include "ConstraintGrammarParser.h"
#include "Constraint.h"
#include "antlr4-runtime.h"
#include <string>

using namespace antlrcpp;

class ConstraintBuilder : public ConstraintGrammarBaseVisitor {
private:
  ConstraintGrammarParser *parser;
  std::string opString(int op);

public:
  ConstraintBuilder(ConstraintGrammarParser *parser);
  std::shared_ptr<Constraint::Constraint> build(ConstraintGrammarParser::ConstraintContext *ctx);

  Any visitSymbolDef(ConstraintGrammarParser::SymbolDefContext *ctx) override; 
  Any visitSymbolExpr(ConstraintGrammarParser::SymbolExprContext *ctx) override; 
  Any visitConstantExpr(ConstraintGrammarParser::ConstantExprContext *ctx) override; 
  Any visitCastExpr(ConstraintGrammarParser::CastExprContext *ctx) override; 
  Any visitUnaryExpr(ConstraintGrammarParser::UnaryExprContext *ctx) override; 
  Any visitBinaryExpr(ConstraintGrammarParser::BinaryExprContext *ctx) override; 

};
