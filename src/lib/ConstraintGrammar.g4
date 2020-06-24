grammar ConstraintGrammar;

/* 
 * Simple grammar for STG constraint
 *  - begins with symbol dictionary which defines type and value for symbol
 *  - then consists of a single logical expression
 *
 * Rule labels are introduced for the visitor pattern.
 * All alternatives in a rule must be labeled, we use "ignore*" to
 * denote where we had to introduce labels but do not need them in 
 * the visitor.
 *
 * Could pretty easily restructure this to make the grammar
 * enforce a coarse typing on this very simple constraint language.
 */

constraint : '[' (symbolDef (',' symbolDef)* )? ']' expr ;

symbolDef : IDENTIFIER ':' TYPE '=' NUMBER ;

expr : leafExpr
     | '(' unaryExpr ')'
     | '(' castExpr ')'
     | '(' binaryExpr ')'
;

leafExpr : constantExpr | symbolExpr ;

symbolExpr : IDENTIFIER ;

constantExpr : '(' TYPE NUMBER ')' ;

castExpr : CASTOP TYPE expr ;

unaryExpr : UNOP expr ;

binaryExpr : BINOP expr expr ;

// Lexical elements are capitalized

BINOP : 'add' 
      | 'sub'
      | 'mul' 
      | 'udiv' 
      | 'sdiv' 
      | 'urem' 
      | 'srem' 
      | 'fadd' 
      | 'fsub' 
      | 'fmul' 
      | 'fdiv' 
      | 'frem' 
      | 'and' 
      | 'or' 
      | 'xor' 
      | 'shl' 
      | 'lshr' 
      | 'ashr' 
      | 'eq' 
      | 'ne' 
      | 'ult' 
      | 'ule' 
      | 'ugt' 
      | 'uge' 
      | 'slt' 
      | 'sle' 
      | 'sgt' 
      | 'sge' 
      | 'oeq' 
      | 'one' 
      | 'olt' 
      | 'ole' 
      | 'ogt' 
      | 'oge' 
      | 'ord' 
      | 'fueq' 
      | 'fune' 
      | 'fult' 
      | 'fule' 
      | 'fugt' 
      | 'fuge' 
      | 'funo' 
      | 'land' 
      | 'lor' 
;

UNOP : 'lnot' 
     | 'fneg' 
;

CASTOP : 'trunc' 
       | 'zext' 
       | 'sext' 
       | 'uitofp' 
       | 'sitofp' 
       | 'fptrunc' 
       | 'fpext' 
       | 'fptoui' 
       | 'fptosi' 
       | 'bitcast' 
;

TYPE : 'i1'
     | 'i8'
     | 'i16'
     | 'i32'
     | 'i64'
     | 'float'	
     | 'double'	
;

NUMBER : INTLIT
       | FLOATLIT
;

// allows leading zeros
INTLIT : SIGN? NOLEADZEROS
;

NOLEADZEROS : '0' | NONZERO
;

NONZERO : [1-9] [0-9]*
;

FLOATLIT : INTLIT ('.' [0-9]+)? ('e' SIGN? NONZERO)? 
;

SIGN : ('+' | '-')
;

IDENTIFIER : [a-zA-Z_][a-zA-Z0-9_]* ;

// Whitespace
WS : [ \t\n\r]+ -> skip ;

COMMENT : '//' ~[\n\r]* -> skip ;
