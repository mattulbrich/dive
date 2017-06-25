grammar Dafny;

options {
  output = AST;
  ASTLabelType = DafnyTree;
}

tokens {
  COMPILATION_UNIT;
  RESULTS;
  ARGS;
  BLOCK;
  CALL;
  FIELD;
  FIELD_ACCESS;
  LISTEX; // not supported currently
  SETEX; // not supported currently
  ARRAY_ACCESS;
  NOETHER_LESS;
  WILDCARD;
}

@parser::header {
  package edu.kit.iti.algover.parser;
}

@lexer::header {
  package edu.kit.iti.algover.parser;
}

// exit upon first error
@parser::members {
  protected void mismatch(IntStream input, int ttype, BitSet follow)
    throws RecognitionException
  {
    throw new MismatchedTokenException(ttype, input);
  }

  public Object recoverFromMismatchedSet(IntStream input,
                                         RecognitionException e,
                                         BitSet follow)
    throws RecognitionException
  {
    throw e;
  }

  protected Object recoverFromMismatchedToken(IntStream input, int ttype, BitSet follow)
    throws RecognitionException
  {
    throw new MismatchedTokenException(ttype, input);
  }

  private BitSet LVALUE_TOKENTYPES = BitSet.of(ID, FIELD_ACCESS, ARRAY_ACCESS);

  private boolean logicMode = false;
  public void setLogicMode(boolean b) { this.logicMode = b; }
}

// exit upon first error
@rulecatch {
  catch (RecognitionException e) {
    throw e;
  }
}

ALL: 'forall';
ASSERT: 'assert';
ASSUME: 'assume';
BOOL : 'bool';
// CASE: 'case'; 
CLASS: 'class';
DECREASES: 'decreases';
ELSE: 'else';
ENSURES: 'ensures';
EX: 'exists';
FALSE: 'false';
FREE: 'free';
FUNCTION: 'function';
IF: 'if';
IN : 'in';
INT : 'int';
INVARIANT: 'invariant';
LABEL: 'label';
LEMMA: 'lemma';
LET: 'let';
METHOD: 'method';
MODIFIES: 'modifies';
NULL: 'null';
// PREDICATE : 'predicate';
REQUIRES: 'requires';
RETURN : 'return';
RETURNS : 'returns';
SEQ : 'seq';
SET : 'set';
THEN: 'then';
THIS: 'this';
TRUE: 'true';
VAR: 'var';
WHILE: 'while';

DOUBLECOLON: '::';
ASSIGN: ':=';
OR: '||';
AND: '&&';
IMPLIES: '==>';
PLUS: '+';
MINUS: '-';
NOT: '!';
TIMES: '*';
UNION: '++';
INTERSECT: '**';
LT: '<';
LE: '<=';
GT: '>';
GE: '>=';
EQ: '==';
NEQ: '!=';
DOT: '.';
BLOCK_BEGIN: '{';
BLOCK_END: '}';
LPAREN: '(';
RPAREN: ')';
LBRACKET: '[';
RBRACKET: ']';

LENGTH: 'Length' ('0' .. '9')*;
ARRAY : 'array' (('1' .. '9') ('0' .. '9')*)?;

ID : ('a' .. 'z' | 'A' .. 'Z' | '_' ) 
     ('a' .. 'z' | 'A' .. 'Z' | '0' .. '9' | '_')*;

LOGIC_ID : ('a' .. 'z' | 'A' .. 'Z' | '_' | '$')
           ('a' .. 'z' | 'A' .. 'Z' | '0' .. '9' | '_' | '$')*;

INT_LIT : ('0' .. '9' ) ('0' .. '9' | '_')*;
// glyph = "`~!@#$%^&*()-_=+[{]}|;:',<.>/?\\".

WS : (' '|'\t'|'\n'|'\r')                     { $channel = HIDDEN; };
SINGLELINE_COMMENT: '//' ~('\r' | '\n')* { $channel = HIDDEN; };
MULTILINE_COMMENT: '/*' .* '*/'          { $channel = HIDDEN; };

label:
  'label'^ ID ':'!
  ;

program:
  // "include"
  (method | function | clazz)+ -> ^(COMPILATION_UNIT clazz* method* function*)
  ;

program_only:
  program EOF -> program
  ;


clazz:
  CLASS^ ID '{'!
    (method | function | field)+
  '}'!
  ;

method:
  ( 'ghost' )?
  tok = ('method' | 'lemma')
  ID '(' vars? ')'
  ( returns_ )?
  ( requires )*
  ( ensures )*
  ( modifies )?
  ( decreases )?
  '{' statements? '}'
  ->
    ^(METHOD[tok] ID ^(ARGS vars?) returns_? requires* ensures*
        decreases? ^(BLOCK statements?))
  ;

function:
  'function'
  ID '(' vars? ')' ':' type
    ( requires )*
    ( ensures )*
  '{' expression '}'
  ->
    ^(FUNCTION ID ^(ARGS vars?) ^(RETURNS type) requires* ensures*
        ^(BLOCK expression?))
  ;

field:
  ( 'ghost' )? 'var' ID ':' type ';'
    -> ^(FIELD ID type)
  ;

vars:
  var
  ( ','! var )*
  ;

var:
  ID ':' type -> ^(VAR ID type)
  ;

// one day this will be "id_param"
type:
    INT | BOOL
  | SET^ '<'! type '>'!
  | ARRAY^ '<'! type '>'!
  | SEQ^ '<'! type '>'!
  | ID
  ;

returns_:
  RETURNS^ '('! vars ')'!
  ;

requires:
  ( FREE )? REQUIRES^ label? expression
  ;

ensures:
  ( FREE )? ENSURES^ label? expression
  ;

decreases:
  DECREASES^ expressions
  ;

invariant:
  INVARIANT^ label? expression
  ;

modifies:
  MODIFIES^ expressions
  ;

block:
  '{' statements? '}' -> ^(BLOCK statements?)
  ;

statements:
  ( statement )+
  ;

statement:
    VAR^ ID ':'! type (':='! expression)? ';'!

  | postfix_expr
      ( ASSIGN value=expression_wildcard ';'
      { if(!LVALUE_TOKENTYPES.member($postfix_expr.tree.getType()))
            throw new MismatchedSetException(LVALUE_TOKENTYPES, input); }
         -> ^(ASSIGN postfix_expr expression_wildcard)
      | ';'
      { if($postfix_expr.tree.getType() != CALL)
            throw new MismatchedTokenException($postfix_expr.start.getType(), input); }
         -> postfix_expr
      )

  | label? WHILE expression_wildcard invariant* modifies? decreases? block
           -> ^(WHILE label? expression_wildcard invariant* modifies? decreases? block)

  | if_statement

  | 'assert'^ ( 'label'! ID ':'! )? expression ';'!

  | 'assume'^ ( 'label'! ID ':'! )? expression ';'!

  | 'return'^ ';'!
  ;


/* ifs are extra since they can be cascaded */
if_statement:
  label? IF expression_wildcard block
  ( -> ^(IF label? expression_wildcard block)
  | ELSE block -> ^(IF label? expression_wildcard block+)
  | ELSE if_statement -> ^(IF label? expression_wildcard block ^(BLOCK if_statement))
  )
  ;
  // not needed any more: ( options { greedy=true; } : 'else' 
  // everything is in blocks now

ids:
  ID (','! ID)+
  ;

//
// ---------------- Expressions!
//

expression_wildcard:
    expression
  | star=TIMES -> WILDCARD[$star]
  ;

expressions:
  expression ( ','! expression )*
  ;

expression:
    equiv_expr
  | endless_expr
  ;

expression_only:
  expression EOF -> expression
  ;

equiv_expr:
  implies_expr ( '<==>'^ implies_expr )*
  ;

// right assoc
implies_expr:
  or_expr ( '==>'^ implies_expr )?
  ;

// left assoc
or_expr:
  and_expr ( '||'^ and_expr )*
  ;

and_expr:
  rel_expr ( '&&'^ rel_expr )*
  ;

rel_expr:
  add_expr ( ( '<'^ | '>'^  | '=='^ | '!='^ |
              '<='^ | '>='^ | 'in'^ | '!in'^ ) add_expr )?
  ;

add_expr:
  mul_expr ( ('+' | '-')^ mul_expr )*
  ;

mul_expr:
  prefix_expr ( ('*' | '/' | '%')^ prefix_expr )*
  ;

prefix_expr:
    '-'^ prefix_expr
  | '!'^ prefix_expr
  | postfix_expr
  ;

endless_expr:
    'if'^ expression 'then'! expression 'else'! expression
  | quantifier
  | let_expr
  ;

let_expr:
  LET ( 'var' )? ID (',' ID)* ':=' expression (',' expression)*
    (';'|'::')  expression
      -> ^(LET ^(VAR ID*) expression+)
  ;

postfix_expr:
  ( atom_expr -> atom_expr )   // see ANTLR ref. page 175
  ( '[' expressions ']' -> ^( ARRAY_ACCESS $postfix_expr expressions )
  | '.' LENGTH -> ^( LENGTH $postfix_expr )
  | '.' ID '(' expressions? ')' -> ^( CALL ID $postfix_expr ^(ARGS expressions?) )
  | '.' ID -> ^( FIELD_ACCESS $postfix_expr ID )
  )*
  ;

atom_expr:
    ID
  | ID '(' expressions? ')' -> ^(CALL ID ^(ARGS expressions?) )
  | {logicMode}? logic_id_param
      (                      -> logic_id_param
      | '(' expressions? ')' -> ^(CALL logic_id_param ^(ARGS expressions?) )
      )
  | TRUE | FALSE | NULL | 'this'
  | INT_LIT
  | 'old'^ '('! expression ')'!
  | 'fresh'^ '('! expression ')'!
//  | '|'^ expression '|'!
  | '('! expression ')'!
  ;

id_param:
    ID^ ( '<'! id_param ( ','! id_param )* '>'! )?
  | INT | BOOL // ...
  ;

// Currently, only logic ids can have type parameters, will change later ...
logic_id_param:
  LOGIC_ID^ ( ( '<' id_param ( ',' id_param )* '>' ) =>
                '<'! id_param ( ','! id_param )* '>'! )?
  ;

quantifier:
  (ALL^ | EX^) ID (','! ID)* ':'! type '::'! expression
  ;
