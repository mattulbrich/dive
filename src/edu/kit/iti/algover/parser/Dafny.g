grammar Dafny;

options { 
  output = AST;
  ASTLabelType = DafnyTree;
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


INT : 'int';
SET : 'set';
RETURNS : 'returns';
ENSURES: 'ensures';
REQUIRES: 'requires';
DECREASES: 'decreases';
METHOD: 'method';
LEMMA: 'lemma';
LABEL: 'label';
ELSE: 'else';
IF: 'if';
THEN: 'then';
WHILE: 'while';
VAR: 'var';
CALL:'call';
INVARIANT: 'invariant';
ASSERT: 'assert';

ALL: 'forall';
EX: 'exists';

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
DOT: '.';
BLOCK_BEGIN: '{';
BLOCK_END: '}';

LENGTH: 'Length' ('0' .. '9')*;
ARRAY : 'array' (('1' .. '9') ('0' .. '9')*)?;
ID : ('a' .. 'z' | 'A' .. 'Z' | '_')+;
LIT : '0' ..'9'+;
WS : (' '|'\n'|'\r') { $channel = HIDDEN; };

program:
  method +
  ;

method:
  tok = ('method' | 'lemma')
  ID '(' vars? ')'
  ( returns_ )?
  ( requires )*
  ( ensures )*
  ( decreases )?
  '{' ( decl )* statements? '}'
  ->
    ^(METHOD[tok] ID ^(ARGS vars?) returns_? requires* ensures* 
        decreases? decl* ^(BLOCK statements?))
  ;

decl:
  VAR! var ';'!
  ;

vars:
  var
  ( ','! var )*
  ;

var:
  ID ':' type -> ^(VAR ID type)
  ;

type:
    INT | SET^ '<'! INT '>'!
  | ARRAY^ '<'! INT '>'!
  ;

returns_:
  RETURNS^ '('! vars ')'!
  ;

requires:
  REQUIRES^ ('label'! ID ':'!)? expression
  ;

ensures:
  ENSURES^ ('label'! ID ':'!)? expression
  ;

decreases:
  DECREASES^ expression
  ;

invariant:
  INVARIANT^ ('label'! ID ':'!)? expression
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
    ID ':='^ expression ';'!
  | (ID ':=' 'call') => r=ID ':=' 'call' f=ID '(' expressions? ')' ';'
        -> ^('call' $f ^(RESULTS $r) ^(ARGS expressions?))
  | ids ':=' 'call' ID '(' expressions? ')' ';'
        -> ^('call' ID ^(RESULTS ids) ^(ARGS expressions?))
  | ('label' ID ':' )? 
      'while' expression invariant+ decreases relaxedBlock
        -> ^('while' ID? expression invariant+ decreases relaxedBlock)
  | 'if'^ expression relaxedBlock
      ( options { greedy=true; } : 'else'! relaxedBlock )?
  | 'assert'^ ( 'label'! ID ':'! )? expression ';'!
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
  add_expr ( ('<'^ | '>'^ | '=='^ | '<='^ | '>='^) add_expr )?
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
  ;

postfix_expr:
  atom_expr
  ( '[' expression ']' -> ^( ARRAY_ACCESS atom_expr expression )
  | '.' LENGTH -> ^( LENGTH atom_expr )
  | -> atom_expr
  )
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
  '('! (ALL^ | EX^) ID ':'! type '::'! expression ')'!
  ;