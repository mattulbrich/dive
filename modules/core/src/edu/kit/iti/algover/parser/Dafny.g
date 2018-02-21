grammar Dafny;

options {
  output = AST;
  ASTLabelType = DafnyTree;
}

tokens {
  COMPILATION_UNIT;
  TYPE;
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
  HEAP_UPDATE;
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

  private boolean schemaMode = false;
  public void setSchemaMode(boolean b) { this.schemaMode = b; }
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
OBJECT : 'object';
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

DOUBLE_BLANK: '__';
BLANK: '_';
ELLIPSIS : '...';
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
AT: '@';
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

SCHEMA_ID : '?' ID;



INT_LIT : ('0' .. '9' ) ('0' .. '9' | '_')*;
// glyph = "`~!@#$%^&*()-_=+[{]}|;:',<.>/?\\".

WS : (' '|'\t'|'\n'|'\r')                { $channel = HIDDEN; };
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
        decreases? modifies? ^(BLOCK statements?))
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
  ( 'ghost' )? 'var' ID ':' typeRef ';'
    -> ^(FIELD ID typeRef)
  ;

vars:
  var
  ( ','! var )*
  ;

var:
  ID ':' typeRef -> ^(VAR ID typeRef)
  ;

// one day this will be "id_param"
type:
    INT | BOOL | OBJECT
  | SET^ '<'! type '>'!
  | ARRAY^ '<'! type '>'!
  | SEQ^ '<'! type '>'!
  | ID^ ( '<'! type ( ','! type )* '>'! )?
  ;

typeRef:
    type -> ^(TYPE type)
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

/* To support var i, j: int read ref manual p. 186:
 When there are some elements with cardinality one and others with
 cardinality greater than one, the elements with cardinality one are
 duplicated as the parser creates the tree. In the following rule, the ’int’
 token has cardinality one and is replicated for every ID token found on
 the input stream:
    decl : 'int' ID (',' ID)* -> ^('int' ID)+ ;
*/
varDecl:
    VAR ID ( ',' ID )+ ':' typeRef ';' -> ^(VAR ID typeRef)+
  | VAR^ ID ( ':'! typeRef (':='! expression)?
           | ':='! expression ) ';'!
  ;

statements:
  ( statement | varDecl )+
  ;

statement:

    postfix_expr
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

  | 'assert'^ label? expression ';'!

  | 'assume'^ label? expression ';'!

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
// ---------------- Sequents ... entry point for logic
//

sequent:
  ante=expressions? '|-' succ=expressions? -> ^(SEQ ^(BLOCK $ante?) ^(BLOCK $succ?))
  ;

//
// ---------------- Expressions!
//

expression_wildcard:
    expression
  | star=TIMES -> WILDCARD[$star]
  ;

expressions:
    expression ( ','! expression )* ( {schemaMode}? ','! DOUBLE_BLANK )?
  | {schemaMode}? DOUBLE_BLANK ( ','! expression )*
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
              '<='^ | '>='^ | 'in'^ | '!in'^ ) add_expr )*
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
  LET ( 'var' )? usual_or_logic_id (',' usual_or_logic_id)* ':=' expression (',' expression)*
    (';'|'::')  expression
      -> ^(LET ^(VAR usual_or_logic_id*) expression+)
  ;

// Apparantly, antlr requires explicit lookaheads for all cases here ...
postfix_expr:
  ( atom_expr -> atom_expr )   // see ANTLR ref. page 175
  ( '[' expression ( {logicMode}? ':=' expression ']'     -> ^( HEAP_UPDATE $postfix_expr expression expression )
                   | ( ',' expression )* ']' -> ^( ARRAY_ACCESS $postfix_expr expression+ )
                   )
  | '.' LENGTH -> ^( LENGTH $postfix_expr )
  | '.' ID '(' expressions? ')' -> ^( CALL ID $postfix_expr ^(ARGS expressions?) )
  | '.' ID -> ^( FIELD_ACCESS $postfix_expr ID )
  )*
  ( '@'  {logicMode}?  heap_postfix_expr -> ^('@' $postfix_expr heap_postfix_expr ) )?
  ;

// This rule has been instantiated to avoid the following error message
// for the '@' in postfix_expr
// Dafny.g:382:78: reference $postfix_expr is ambiguous; rule postfix_expr is enclosing rule and referenced in the production (assuming enclosing rule)
heap_postfix_expr:
  postfix_expr
  ;

atom_expr:

  usual_or_logic_id
    (                      -> usual_or_logic_id
    | '(' expressions? ')' -> ^(CALL usual_or_logic_id ^(ARGS expressions?) )
    )
  | {schemaMode}?
  ( SCHEMA_ID | BLANK | ELLIPSIS^ expression ELLIPSIS! )

  | TRUE | FALSE | NULL | 'this'
  | INT_LIT
  | 'old'^ '('! expression ')'!
  | 'fresh'^ '('! expression ')'!
//  | '|'^ expression '|'!
  | '('! expression ')'!
  ;

// Either usual or logic id
usual_or_logic_id:
    ID
  | {logicMode}? logic_id_param
  ;

// Currently, only logic ids can have type parameters, will change later ...
logic_id_param:
  LOGIC_ID^ ( ( '<' type ( ',' type )* '>' ) =>
                '<'! type ( ','! type )* '>'! )?
  ;

quantifier:
  (ALL^ | EX^) ID (','! ID)* ( ':'! typeRef )? '::'! expression
  ;
