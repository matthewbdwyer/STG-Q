grammar ConstraintGrammar;

/* 
 * Simple grammar for STG constraint
 *  - begins with symbol dictionary which defines type, value and min, 
 *    max range for symbol
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

// symbolDef : IDENTIFIER ':' TYPE '=' NUMBER ', R:[' NUMBER ',' NUMBER'], D:[' NUMBER ',' NUMBER ',' NUMBER']';

/*
 * Some comments about the above rule
 *   1) The rule makes ranges and distributions required, we might want them
 *      to be options with a default value, e.g., min/max, uniform
 *   2) The tokenization of the rule is very restrictive.  Writing ', R:[' 
 *      forces the whitespace to be a single character.  Grammar's should
 *      be written to allow for arbitrary whitespace.
 * Here is an alternative version that resolves these issues.
 */
// symbolDef : IDENTIFIER ':' TYPE '=' NUMBER | IDENTIFIER ':' TYPE ;

symbolDef : IDENTIFIER ':' TYPE ('=' NUMBER)?;

/*
 * This allows the range and distribution specs to be optional through the 
 * use of the '?' in the symbolDef rule.
 *
 * Each individual symbol is now its own token allowing for arbitrary 
 * whitespace.
 *
 * The syntax is a bit more explicit, changing R to range, and there is
 * less overloading, i.e., [] changed to () for distributions.  The former
 * is the notation for an interval and the latter for parameterization.
 *
 * It pulls the distribution specs out into a set of separate rules.
 * This allows the number of parameters to be matched to the distribution.
 *
 * A consequence of the above is that now a symbolDef is more complicated.
 * This means that you probably want to think about enhancing the AST
 * representation in Constraint.h to define node types for symbol defs
 * and dictionaries.  Then extending the Constraint builder, printer, etc.
 * accordingly.
 */

expr : leafExpr
     | '(' unaryExpr ')'
     | '(' castExpr ')'
     | '(' unIntrExpr ')'     // unary intrinsic expression
     | '(' binaryExpr ')'
     | '(' binIntrExpr ')'   // binary intrinsic expression
;

leafExpr : constantExpr | symbolExpr ;

symbolExpr : IDENTIFIER ;

constantExpr : '(' TYPE NUMBER ')' ;

castExpr : CASTOP TYPE expr ;

unaryExpr : UNOP expr ;

binaryExpr : BINOP expr expr ;

// changed by SBH

binIntrExpr : BININTRFUN TYPE expr expr ;
unIntrExpr : UNINTRFUN TYPE expr ;   //the type is necessary because no way we can predict the return type of the call seeing the parameters type


UNINTRFUN : 'llvm.sin.f32'
          | 'llvm.sin.f64'
          | 'llvm.sin.f80'
          | 'llvm.sin.f128'
          | 'llvm.sin.ppcf128'
          | 'llvm.cos.f32'
          | 'llvm.cos.f64'
          | 'llvm.cos.f80'
          | 'llvm.cos.f128'
          | 'llvm.cos.ppcf128'
          | 'llvm.exp.f32'
          | 'llvm.exp.f64'
          | 'llvm.exp.f80'
          | 'llvm.exp.f128'
          | 'llvm.exp.ppcf128'
          | 'llvm.exp2.f32'
          | 'llvm.exp2.f64'
          | 'llvm.exp2.f80'
          | 'llvm.exp2.f128'
          | 'llvm.exp2.ppcf128'
          | 'llvm.log.f32'
          | 'llvm.log.f64'
          | 'llvm.log.f80'
          | 'llvm.log.f128'
          | 'llvm.log.ppcf128'
          | 'llvm.log10.f32'
          | 'llvm.log10.f64'
          | 'llvm.log10.f80'
          | 'llvm.log10.f128'
          | 'llvm.log10.ppcf128'
          | 'llvm.log2.f32'
          | 'llvm.log2.f64'
          | 'llvm.log2.f80'
          | 'llvm.log2.f128'
          | 'llvm.log2.ppcf128'
          | 'llvm.fabs.f32'
          | 'llvm.fabs.f64'
          | 'llvm.fabs.f80'
          | 'llvm.fabs.f128'
          | 'llvm.fabs.ppcf128'
          | 'llvm.sqrt.f32'
          | 'llvm.sqrt.f64'
          | 'llvm.sqrt.f80'
          | 'llvm.sqrt.f128'
          | 'llvm.sqrt.ppcf128'
          | 'llvm.floor.f32'
          | 'llvm.floor.f64'
          | 'llvm.floor.f80'
          | 'llvm.floor.f128'
          | 'llvm.floor.ppcf128'
          | 'llvm.ceil.f32'
          | 'llvm.ceil.f64'
          | 'llvm.ceil.f80'
          | 'llvm.ceil.f128'
          | 'llvm.ceil.ppcf128'
          | 'sin'
          | 'cos'
          | 'tan.f32'
          | 'tan'
          | 'exp'
          | 'expf'
          | 'log'
          | 'log10f'
          | 'log2f'
          | 'sqrt'
;

BININTRFUN : 'llvm.pow.f32'
           | 'llvm.pow.f64'
           | 'llvm.pow.f80'
           | 'llvm.pow.f128'
           | 'llvm.pow.ppcf128'
           | 'atan2.f32'
           | 'atan2'
           | 'llvm.powi.f32'
           | 'llvm.powi.f64'
           | 'llvm.powi.f80'
           | 'llvm.powi.f128'
           | 'llvm.powi.ppcf128'
           | 'llvm.fma.f32'
           | 'llvm.fma.f64'
           | 'llvm.fma.f80'
           | 'llvm.fma.f128'
           | 'llvm.fma.ppcf128'
           | 'llvm.minnum.f32'
           | 'llvm.minnum.f64'
           | 'llvm.minnum.f80'
           | 'llvm.minnum.f128'
           | 'llvm.minnum.ppcf128'
           | 'llvm.maxnum.f32'
           | 'llvm.maxnum.f64'
           | 'llvm.maxnum.f80'
           | 'llvm.maxnum.f128'
           | 'llvm.maxnum.ppcf128'
           | 'llvm.minimum.f32'
           | 'llvm.minimum.f64'
           | 'llvm.minimum.f80'
           | 'llvm.minimum.f128'
           | 'llvm.minimum.ppcf128'
           | 'llvm.maximum.f32'
           | 'llvm.maximum.f64'
           | 'llvm.maximum.f80'
           | 'llvm.maximum.f128'
           | 'llvm.maximum.ppcf128'
           | 'llvm.copysign.f32'
           | 'llvm.copysign.f64'
           | 'llvm.copysign.f80'
           | 'llvm.copysign.f128'
           | 'llvm.copysign.ppcf128'
           | 'pow'
;

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
