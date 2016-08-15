grammar Dafny;

options {
  output = AST;
  ASTLabelType = DafnyTree;
}

tokens {
  RESULTS;
  ARGS;
  BLOCK;
  FIELD_ACCESS;
  LISTEX; // not supported currently
  SETEX; // not supported currently
  ARRAY_ACCESS;
  ARRAY_UPDATE;
  OBJ_FUNC_CALL;
  FUNC_CALL;
  HAVOC;
  NOETHER_LESS;
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
CALL: 'call';
// CASE: 'case'; 
CLASS: 'class';
DECREASES: 'decreases';
ELSE: 'else';
ENSURES: 'ensures';
EX: 'exists';
FIELD: 'classfield';
FUNCTION: 'function';
IF: 'if';
INT : 'int';
INVARIANT: 'invariant';
LABEL: 'label';
LEMMA: 'lemma';
METHOD: 'method';
MODIFIES: 'modifies';
NULL: 'null';
// PREDICATE : 'predicate';
REQUIRES: 'requires';
RETURNS : 'returns';
SEQ : 'seq';
SET : 'set';
THEN: 'then';
THIS: 'this';
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
ID : ('a' .. 'z' | 'A' .. 'Z' | '_') ('a' .. 'z' | 'A' .. 'Z' | '0' .. '9' | '_')*;
INT_LIT : ('0' .. '9' ) ('0' .. '9' | '_')*;
// glyph = "`~!@#$%^&*()-_=+[{]}|;:',<.>/?\\".

WS : (' '|'\n'|'\r')                     { $channel = HIDDEN; };
SINGLELINE_COMMENT: '//' ~('\r' | '\n')* { $channel = HIDDEN; };
MULTILINE_COMMENT: '/*' .* '*/'          { $channel = HIDDEN; };

label:
  'label'^ ID ':'!
  ;

program:
  // "include"
  (method | function | clazz)+
  ;


clazz:
  CLASS^ ID '{'!
    (method | function | field)+
  '}'!
  ;

method:
  tok = ('method' | 'lemma')
  ID '(' vars? ')'
  ( returns_ )?
  ( requires )*
  ( ensures )*
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
  'var' ID ':' type ';'
    -> ^(FIELD ID type)
  ;

vars:
  var
  ( ','! var )*
  ;

var:
  ID ':' type -> ^(VAR ID type)
  ;

type:
    INT | BOOL | SET^ '<'! INT '>'!
  | ARRAY^ '<'! INT '>'!
  | SEQ^ '<'! INT '>'!
  ;

returns_:
  RETURNS^ '('! vars ')'!
  ;

requires:
  REQUIRES^ label? expression
  ;

ensures:
  ENSURES^ label? expression
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

relaxedBlock:
    block
  | statement -> ^(BLOCK statement)
  ;

statements:
  ( statement )+
  ;

statement:
    VAR^ ID ':'! type (':='! expression)? ';'!
  | ID ass=':=' '*' ';' -> ^(HAVOC[$ass] ID)
  | ID ':='^ expression ';'!
  | ID '[' i=expression ']' ass=':=' v=expression ';'
        -> ^(ARRAY_UPDATE[$ass] ID $i $v)
  | (ID ':=' 'call') => r=ID ':=' 'call' f=ID '(' expressions? ')' ';'
        -> ^('call' $f ^(RESULTS $r) ^(ARGS expressions?))
  | ids ':=' 'call' ID '(' expressions? ')' ';'
        -> ^('call' ID ^(RESULTS ids) ^(ARGS expressions?))
  | label?
      'while' expression invariant+ modifies? decreases relaxedBlock
        -> ^('while' label? expression invariant+ modifies? decreases relaxedBlock)
  | label? 'if'^ expression relaxedBlock
      ( options { greedy=true; } : 'else'! relaxedBlock )?
  | 'assert'^ ( 'label'! ID ':'! )? expression ';'!
  | 'assume'^ ( 'label'! ID ':'! )? expression ';'!
  ;

ids:
  ID (','! ID)+
  ;

expressions:
  expression ( ','! expression )*
  ;

expression:
  or_expr;

or_expr:
  and_expr ( ('||'^ | '==>'^) or_expr )?
  ;

and_expr:
  rel_expr ( '&&'^ and_expr )?
  ;

rel_expr:
  add_expr ( ('<'^ | '>'^ | '=='^ | '!='^ | '<='^ | '>='^) add_expr )?
  ;

add_expr:
  mul_expr ( ('+' | '-' | '++')^ add_expr )?
  ;

mul_expr:
  prefix_expr ( ('*' | '**')^ mul_expr )?
  ;

prefix_expr:
    '-'^ prefix_expr
  | '!'^ prefix_expr
  | postfix_expr
  | quantifier
  ;

postfix_expr:
  ( atom_expr -> atom_expr )
  ( '[' expression ']' -> ^( ARRAY_ACCESS atom_expr expression )
  | '.' LENGTH -> ^( LENGTH atom_expr )
  | '.' ID '(' expressions ')' -> ^( OBJ_FUNC_CALL ID atom_expr expressions )
  | '.' ID -> ^( FIELD_ACCESS atom_expr ID )
  )*
  ;

expression_only:
  expression EOF -> expression
  ;


atom_expr:
    ID
  | ID '(' expressions ')' -> ^(FUNC_CALL ID expressions)
  | INT_LIT
  | 'this'
  | NULL
  | '('! expression ')'!
  ;

quantifier:
  '('! (ALL^ | EX^) ID ':'! type '::'! expression ')'!
  ;
