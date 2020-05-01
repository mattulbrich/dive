grammar Dafny;

options {
  output = AST;
  ASTLabelType = DafnyTree;
}

tokens {
  COMPILATION_UNIT;
  TYPE;
  ARGS;
  BLOCK;
  CALL;
  FIELD;
  FIELD_ACCESS;
  LISTEX;
  SETEX;
  MULTISETEX; // not supported currently
  ARRAY_ACCESS;
  NOETHER_LESS;
  WILDCARD;
  HEAP_UPDATE;
  TYPED_SCHEMA;
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


@lexer::members {
  @Override
  public void reportError(RecognitionException e) {
    throw new RuntimeException(e);
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
// CASE: 'case';
CLASS: 'class';
DECREASES: 'decreases';
ELSE: 'else';
ENSURES: 'ensures';
EX: 'exists';
FALSE: 'false';
FREE: 'free';
FRESH: 'fresh';
FUNCTION: 'function';
GHOST: 'ghost';
IF: 'if';
IN : 'in';
INCLUDE : 'include';
INT : 'int';
INVARIANT: 'invariant';
LABEL: 'label';
LEMMA: 'lemma';
LET: 'let';
METHOD: 'method';
MODIFIES: 'modifies';
MULTISET: 'multiset';
NEW: 'new';
NOTIN: '!in';
NULL: 'null';
OBJECT : 'object';
OLD : 'old';
// PREDICATE : 'predicate';
PRINT : 'print';
READS : 'reads';
REQUIRES: 'requires';
RETURN : 'return';
RETURNS : 'returns';
SEQ : 'seq';
SET : 'set';
SETTINGS : 'settings';
SUBSUME : 'subsume';
THEN: 'then';
THIS: 'this';
TRUE: 'true';
VAR: 'var';
WHILE: 'while';

DOUBLE_BLANK: '__';
BLANK: '_';
ELLIPSIS: '...';
DOTDOT: '..';
DOUBLECOLON: '::';
ASSIGN: ':=';
OR: '||';
AND: '&&';
IMPLIES: '==>';
PLUS: '+';
MINUS: '-';
NOT: '!';
TIMES: '*';
DIV: '/';
MODULO: '%';
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
CARD: '|';

LENGTH: 'Length' ('0' .. '9')*;
ARRAY : 'array' (('1' .. '9') ('0' .. '9')*)?;

// Is resolved by a syntactic sugar visitor: ResolveUnicodeVisitor!
UNICODE_INDEXED_ID : ID ('\u2080' .. '\u2089')+;

ID : ('a' .. 'z' | 'A' .. 'Z' | '_' )
     ('a' .. 'z' | 'A' .. 'Z' | '0' .. '9' | '_')*;

LOGIC_ID : ('a' .. 'z' | 'A' .. 'Z' | '_' | '$')
           ('a' .. 'z' | 'A' .. 'Z' | '0' .. '9' | '_' | '$')*;

SCHEMA_ID : '?' ID;


INT_LIT : ('0' .. '9' ) ('0' .. '9' | '_')*;
// glyph = "`~!@#$%^&*()-_=+[{]}|;:',<.>/?\\".


fragment HEXDIGIT : '0'..'9' |'a'..'f' |'A'..'F' ;
fragment STRING_CHAR : ~( '"' | '\\' | '\n' | '\r' ) ;
STRING_LIT :
      '"'
      ( STRING_CHAR
        | '\\\'' | '\\\"' | '\\\\' | '\\0' | '\\n' | '\\r' | '\\t'
        | '\\u' HEXDIGIT HEXDIGIT HEXDIGIT HEXDIGIT
      )*
      '"'
      ;


WS : (' '|'\t'|'\n'|'\r')                { $channel = HIDDEN; };
ALGOVER_COMMENT: '//>'                { $channel = HIDDEN; };
SINGLELINE_COMMENT: '//' ( ~('>'|'\r'|'\n') ~('\r' | '\n')* )?
                                         { $channel = HIDDEN; };
MULTILINE_COMMENT: '/*' .* '*/'          { $channel = HIDDEN; };

MULTILINE_COMMENT_BEGIN: '/*' ~('\n')* EOF { $channel = HIDDEN; };

UNKNOWN_CHARACTER: .;

label:
  'label'^ ID ':'!
  ;

include:
    INCLUDE^ STRING_LIT
  | SUBSUME^ STRING_LIT
  ;

settings:
  SETTINGS '{' settings_entry (',' settings_entry)* '}'
    -> ^(SETTINGS settings_entry*)
  ;

settings_entry:
  key=(ID | STRING_LIT) '=' value=(ID | STRING_LIT | INT_LIT)
          -> ^($key $value)
  ;

program:
  (include | settings)*
  (method | function | clazz)*
      -> ^(COMPILATION_UNIT include* settings* clazz* method* function*)
  ;

program_only:
  program EOF -> program
  ;

clazz:
  CLASS^ ID '{'!
    (method | function | field)*
  '}'!
  ;

method:
  ( GHOST )?
  tok = ('method' | 'lemma')
  ID '(' vars? ')'
  ( returns_ )?
  ( ( requires
    | ensures
    | {stream_modifies.size()<1}? => modifies
    | {stream_decreases.size()<1}? => decreases
    )
    ( ';' )?
  )*
  '{' statements? '}'
  ->
    ^(METHOD[tok] ID ^(ARGS vars?) returns_? requires* ensures*
        decreases? modifies? ^(BLOCK statements?))
  ;

function:
  'function' 'method'?
  ID '(' vars? ')' ':' type
    ( requires | ensures | decreases | reads )*
  '{' expression '}'
  ->
    ^(FUNCTION ID ^(ARGS vars?) ^(RETURNS type) requires* ensures* decreases* reads*
        expression)
  ;

field:
  ( GHOST )? 'var' ID ':' typeRef (';')?
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

reads:
  READS^ expressions
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
    ( GHOST )? VAR ID ( ',' ID )+ ':' typeRef ';' -> ^(VAR ID typeRef)+
  | ( GHOST! )? VAR^ ID ( ':'! typeRef (':='! (expression | new_expression))?
                       | ':='! (expression | new_expression) ) ';'!
  ;

statements:
  ( statement | varDecl )+
  ;

statement:

    (lvalue ASSIGN) => lvalue ASSIGN
      (  expression_wildcard ';' -> ^(ASSIGN lvalue expression_wildcard)
      |  new_expression ';' -> ^(ASSIGN lvalue new_expression)
      )

  | (lvalue ',') => lvalue (',' lvalue)+ ASSIGN call_statement
      -> ^(ASSIGN lvalue+ call_statement)

  | call_statement

  | (label? WHILE) =>
    label? WHILE expression_wildcard
        (( invariant
         | {stream_modifies.size()<1}? => modifies
         | {stream_decreases.size()<1}? => decreases
         ) ( ';' )?
        )*
        block
           -> ^(WHILE label? expression_wildcard invariant* modifies? decreases? block)

  | if_statement

  | 'assert'^ label? expression ';'!

  | 'assume'^ label? expression ';'!

  | 'return'^ ';'!

  | 'print'^ expressions ';'!
  ;

call_statement:
    ( usual_or_logic_id '(' ) => usual_or_logic_id '(' expressions? ')' ';' -> ^( CALL usual_or_logic_id ^(ARGS expressions?) )
  | ( atom_expr -> atom_expr )   // see ANTLR ref. page 175
    ( ( '.' ID -> ^( FIELD_ACCESS $call_statement ID )
      | '[' expression ( ',' expression )* ']' -> ^( ARRAY_ACCESS $call_statement expression+ )
      )*
      '.' ID '(' expressions? ')' -> ^( CALL ID $call_statement ^(ARGS expressions?) )
    )+ ';'
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
  ante=expressions? '|-' succ=expressions? EOF -> ^(SEQ ^(BLOCK $ante?) ^(BLOCK $succ?))
  ;

//
// ---------------- Expressions!
//

expression_wildcard:
    expression
  | star=TIMES -> WILDCARD[$star]
  ;

expressions:
    expression ( ','! expression )* ( {schemaMode}? => ','! DOUBLE_BLANK )?
  | {schemaMode}? => DOUBLE_BLANK ( ','! expression )*
  ;

expression:
    equiv_expr
  ;

expression_only:
  expression EOF -> expression
  ;

equiv_expr:
  implies_expr ( ('<==>') => '<==>'^ implies_expr )*
  ;

// right assoc
implies_expr:
  or_expr ( ('==>') => '==>'^ implies_expr )?
  ;

// left assoc
or_expr:
  and_expr ( ('||') => '||'^ and_expr )*
  ;

and_expr:
  rel_expr ( ('&&') => '&&'^ rel_expr )*
  ;

rel_op: ( '<' | '>'  | '==' | '!=' | '<=' | '>=' | 'in' | '!in' ) ;
rel_expr:
  add_expr ( (rel_op) => rel_op^ add_expr )*
  ;

add_op: ('+' | '-') ;
add_expr:
  mul_expr ( (add_op) => add_op^ mul_expr )*
  ;

mul_op: ('*' | '/' | '%') ;
mul_expr:
  prefix_expr ( (mul_op) => mul_op^ prefix_expr )*
  ;

prefix_expr:
    ( '-'^ | '!'^ ) prefix_expr
  | postfix_expr
  | endless_expr
  ;

endless_expr:
    'if'^ expression 'then'! expression 'else'! expression
  | quantifier
  | let_expr
  ;

let_expr:
  LET ( 'var' )? usual_or_logic_id_or_this (',' usual_or_logic_id_or_this)* ':=' expression (',' expression)*
    (';'|'::')  expression
      -> ^(LET ^(VAR usual_or_logic_id_or_this+) expression+)
  ;

// in logic (not in programs!) it is allowed to write "let this := a ; ..."
usual_or_logic_id_or_this:
    usual_or_logic_id
  | {logicMode}? t=THIS -> ^(ID[t])
  ;

postfix_expr:
  ( atom_expr -> atom_expr )   // see ANTLR ref. page 175
  ( '[' expression ( {logicMode}? ':=' expression ']'     -> ^( HEAP_UPDATE $postfix_expr expression expression )
                   | ( ',' expression )* ']' -> ^( ARRAY_ACCESS $postfix_expr expression+ )
                   | '..' expression? ']' -> ^( ARRAY_ACCESS $postfix_expr ^('..' expression+))
                   )
  | '[' '..' expression? ']' -> ^( ARRAY_ACCESS $postfix_expr ^('..' ARGS expression?) )
  | '.' LENGTH -> ^( LENGTH $postfix_expr )
  | '.' ID '(' expressions? ')' -> ^( CALL ID $postfix_expr ^(ARGS expressions?) )
  | '.' ID -> ^( FIELD_ACCESS $postfix_expr ID )
  )*
  ( '@'  {logicMode}?  heap_postfix_expr -> ^('@' $postfix_expr heap_postfix_expr ) )?
  ;

// very similar to postfix_expr
lvalue:
    ID^
  | ( atom_expr -> atom_expr )   // see ANTLR ref. page 175
    (  ( '.' ID '(' expressions? ')' -> ^( CALL ID $lvalue ^(ARGS expressions?) ) )*
       ( '[' expression ( ',' expression )* ']' -> ^( ARRAY_ACCESS $lvalue expression+ )
       | '.' ID -> ^( FIELD_ACCESS $lvalue ID )
       )
    )+
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
  | {schemaMode}? =>
      ( schema_entity
        (    -> schema_entity
        | '(' ':' type ')' -> ^(TYPED_SCHEMA schema_entity type)
        )
      )
  | TRUE | FALSE | NULL | 'this'
  | INT_LIT
  | STRING_LIT
  | 'old'^ '('! expression ')'!
  | 'fresh'^ '('! expression ')'!
  | '|'^ expression '|'!
  | '('! expression ')'!
  | t='{' ( expression ( ',' expression )* )? '}' -> ^(SETEX[t] expression*)
  | t='[' ( expression ( ',' expression )* )? ']' -> ^(LISTEX[t] expression*)
  | 'multiset' '{' expression ( ',' expression )* '}' -> ^(MULTISETEX expression+)
  ;

schema_entity:
  SCHEMA_ID | BLANK | ELLIPSIS^ expression ELLIPSIS! | '('! SCHEMA_ID^ ':'! expression ')'!
  ;

// Either usual or logic id
usual_or_logic_id:
    ID
  | {logicMode}? logic_id_param
  | {logicMode}? UNICODE_INDEXED_ID
  ;

// Currently, only logic ids can have type parameters, will change later ...
logic_id_param:
  LOGIC_ID^ ( ( '<' type ( ',' type )* '>' ) =>
                '<'! type ( ','! type )* '>'! )?
  ;

quantifier:
  (ALL^ | EX^) ID (','! ID)* ( ':'! typeRef )?  ( quantifier_guard )? '::'! expression
  ;

quantifier_guard:
  '|'^ expression
  ;

new_expression:
  'new' ( clss=ID ( '.' meth=ID '(' expressions? ')'
                     -> ^( 'new' $clss ^(CALL $meth? ^(ARGS expressions?) ))
                  |    -> ^( 'new' $clss )
                  )
        | t=(ID|INT|BOOL) '[' expression ']' -> ^( 'new' ^(ARRAY_ACCESS $t expression) )
        )
  ;
