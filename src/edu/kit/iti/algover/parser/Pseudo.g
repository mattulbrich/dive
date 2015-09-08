grammar Pseudo;

options { 
  output = AST;
  ASTLabelType = PseudoTree;
}

tokens {
  RESULTS;
  ARGS;
  BLOCK;
  LISTEX;
  SETEX;
  ARRAY_ACCESS;
}

@parser::header {
  package edu.kit.iti.algover.parser;
}

@lexer::header {
  package edu.kit.iti.algover.parser;
}

INT : 'int';
SET : 'set';
ARRAY : 'array';
RETURNS : 'returns';
ENSURES: 'ensures';
REQUIRES: 'requires';
DECREASES: 'decreases';
FUNCTION: 'function';
ELSE: 'else';
IF: 'if';
THEN: 'then';
WHILE: 'while';
VAR: 'var';
NOT: 'not';
CALL:'call';
INVARIANT: 'invariant';
ASSERT: 'assert';

ALL: '\\all';
EX: '\\ex';

ASSIGN: ':=';
OR: '||';
AND: '&&';
IMPLIES: '==>';
PLUS: '+';
MINUS: '-';
TIMES: '*';
UNION: '++';
INTERSECT: '**';
LT: '<';
LE: '<=';
GT: '>';
GE: '>=';
EQ: '=';

ID : 'a' .. 'z'+;
LIT : '0' ..'9'+;
WS : (' '|'\n'|'\r') { $channel = HIDDEN; };

program:
  function +
  ;

function:
  'function' ID '(' vars? ')'
  ( return_ )?
  ( requires )*
  ( ensures )*
  ( decreases )?
  ( decl )?
  block
  ->
    ^('function' ID ^(ARGS vars?) return_? requires* ensures* 
        decreases? decl? block)
  ;

vars:
  var
  ( ','! var )*
  ;

var:
  ID ':' type -> ^(VAR ID type)
  ;

type:
  INT | SET | ARRAY
  ;

return_:
  RETURNS^ vars
  ;

requires:
  REQUIRES^ (ID ':'!)? expression
  ;

ensures:
  ENSURES^ (ID ':'!)? expression
  ;

decreases:
  DECREASES^ expression
  ;

invariant:
  INVARIANT^ (ID ':'!)? expression
  ;

decl:
  VAR^ vars
  ;

block:
  'begin' statements 'end' -> ^(BLOCK statements)
  ;

relaxedBlock:
    block
  | statement -> ^(BLOCK statement)
  ;

statements:
  statement ( ';'! statement )*
  ;

statement:
    ID ':='^ expression
  | (ID ':=' 'call') => r=ID ':=' 'call' f=ID '(' expressions? ')'
        -> ^('call' $f ^(RESULTS $r) ^(ARGS expressions?))
  | ids ':=' 'call' ID '(' expressions? ')'
        -> ^('call' ID ^(RESULTS ids) ^(ARGS expressions?))
  | 'while'^ expression
      invariant+
      decreases
      'do'! relaxedBlock
  | 'if'^ expression 'then'! relaxedBlock
      ( options { greedy=true; } : 'else'! relaxedBlock )?
  | 'assert'^ ( ID ':'! )? expression
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
  add_expr ( ('<'^ | '>'^ | '='^ | '<='^ | '>='^) add_expr )?
  ;

add_expr:
  mul_expr ( ('+' | '-' | '++')^ add_expr )?
  ;

mul_expr:
  prefix_expr ( ('*' | '**')^ mul_expr )?
  ;

prefix_expr:
    '-'^ prefix_expr
  | 'not'^ prefix_expr
  | postfix_expr
  ;

postfix_expr:
  atom_expr
  ( '[' expression ']' -> ^( ARRAY_ACCESS atom_expr expression )
  | -> atom_expr)
  ;

atom_expr:
    ID
  | LIT
  | quantifier
  | '('! expression ')'!
  | '{' expressions? '}' -> ^(SETEX expressions?)
  | '[' expressions? ']' -> ^(LISTEX expressions?)
  ;

quantifier:
  '('! (ALL^ | EX^) ID ':'! type ';'! expression ')'!
  ;