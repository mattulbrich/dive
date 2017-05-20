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
FREE: 'free';
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

  | expression
      ( ASSIGN value=expression_wildcard ';'
      { if(!LVALUE_TOKENTYPES.member($expression.tree.getType()))
            throw new MismatchedSetException(LVALUE_TOKENTYPES, input); }
         -> ^(ASSIGN expression expression_wildcard)
      | ';'
      { if($expression.tree.getType() != CALL)
            throw new MismatchedTokenException($expression.start.getType(), input); }
         -> expression
      )

  | label? 
      ( WHILE expression_wildcard invariant* modifies? decreases? block
           -> ^(WHILE label? expression_wildcard invariant* modifies? decreases? block)
      | IF expression_wildcard block
         ( options { greedy=true; } : 'else' block )?
           -> ^(IF label? expression_wildcard block*)
      )

  | 'assert'^ ( 'label'! ID ':'! )? expression ';'!

  | 'assume'^ ( 'label'! ID ':'! )? expression ';'!
  ;

ids:
  ID (','! ID)+
  ;

expression_wildcard:
    expression
  | star=TIMES -> WILDCARD[$star]
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
  ( atom_expr -> atom_expr )   // see ANTLR ref. page 175
  ( '[' expression ']' -> ^( ARRAY_ACCESS $postfix_expr expression )
  | '.' LENGTH -> ^( LENGTH $postfix_expr )
  | '.' ID '(' expressions? ')' -> ^( CALL ID $postfix_expr ^(ARGS expressions?) )
  | '.' ID -> ^( FIELD_ACCESS $postfix_expr ID )
  )*
  ;

expression_only:
  expression EOF -> expression
  ;


atom_expr:
    ID
  | ID '(' expressions? ')' -> ^(CALL ID ^(ARGS expressions?) )
  | INT_LIT
  | 'this'
  | NULL
  | '('! expression ')'!
  ;

quantifier:
  '('! (ALL^ | EX^) ID ':'! type '::'! expression ')'!
  ;
