grammar ScriptLanguage;
/*start
    : stmtList
    ;
*/

start
    :   script
    ;

script
    : SCRIPT name=ID '(' signature=argList? ')' INDENT body=stmtList DEDENT
    | stmtList
    ;


argList
    :   varDecl (',' varDecl)*
    ;

varDecl
    :   name=ID ':' type=ID
    ;

stmtList
    :   statement*
    ;


statement
    :   //scriptDecl
         assignment
   // |   repeatStmt
    |   casesStmt
   // |   forEachStmt
   // |   theOnlyStmt
    |   scriptCommand
  //  |   callStmt
    ;

/*scriptDecl
    :
    SCRIPT name=ID '(' signature=argList? ')' INDENT body=stmtList DEDENT
    ;
*/
assignment
    :   variable=ID COLON type=ID SEMICOLON
    |   variable=ID (COLON type=ID)? ASSIGN expression SEMICOLON
    ;

expression
    :
        MINUS expression   #exprNegate
    |   NOT expression  #exprNot
    |   expression '[' substExpressionList ']'  #exprSubst
    |   expression MUL expression #exprMultiplication
    |   <assoc=right> expression DIV expression #exprDivision
    |   expression op=(PLUS|MINUS) expression #exprLineOperators
    |   expression op=(LE|GE|LEQ|GEQ) expression #exprComparison
    |   expression op=(NEQ|EQ) expression  #exprEquality
    |   expression AND expression   #exprAnd
    |   expression OR expression    #exprOr
    |   expression IMP expression   #exprIMP
    //|   expression EQUIV expression already covered by EQ/NEQ
    |   '(' expression ')' #exprParen
    | literals             #exprLiterals
    | matchPattern         #exprMatch
;


substExpressionList
    :
    scriptVar '/' expression (',' substExpressionList)*
    ;

literals :
        ID             #literalID
    |   DIGITS         #literalDigits
    |   TERM_LITERAL   #literalTerm
    |   STRING_LITERAL #literalString
    |   TRUE           #literalTrue
    |   FALSE          #literalFalse
;

/**
 * Example: <pre>
    match `f(x) ==>` using [x:term]

     </pre>*/
matchPattern
    :
       MATCH (
         derivable=DERIVABLE derivableExpression=expression
       | (pattern=expression (USING LBRACKET argList RBRACKET)?)
       )
    ;

scriptVar
    :   '?' ID
    ;

/*repeatStmt
    :   REPEAT INDENT stmtList DEDENT
    ;
*/
casesStmt
    :   CASES INDENT
            casesList*
        (DEFAULT  COLON? INDENT
            defList=stmtList
          DEDENT)?
        DEDENT
    ;

casesList
  //  : simpleCase
   // | closableCase
    :   CASE  (ISCLOSED | expression) COLON? INDENT stmtList DEDENT
    ;
/*simpleCase
    : CASE expression COLON? INDENT stmtList DEDENT
    ;
closableCase
    : CASE MATCH ISCLOSED COLON? INDENT stmtList DEDENT
    ;
*/
/*forEachStmt
    :   FOREACH INDENT stmtList DEDENT
    ;

theOnlyStmt
    :   THEONLY INDENT stmtList DEDENT
    ;
    */

scriptCommand
    :   cmd=ID parameters? SEMICOLON
    ;

parameters: parameter+;
parameter :  ((pname=ID '=')? expr=expression);

/*
callStmt
    :   CALL scriptCommand SEMICOLON
    ;
*/

//LEXER Rules
WS : [ \t\n\r]+ -> channel(HIDDEN) ;

//comments, allowing nesting.
SINGLE_LINE_COMMENT : '//' ~[\r\n]* -> channel(HIDDEN);
MULTI_LINE_COMMENT  : '/*' (MULTI_LINE_COMMENT|.)*? '*/' -> channel(HIDDEN);

CASES: 'cases';
CASE: 'case';
ISCLOSED: 'isCloseable';
DERIVABLE : 'derivable';
DEFAULT: 'default';
ASSIGN : ':=';
LBRACKET: '[';
RBRACKET:']';
USING : 'using';
MATCH : 'match';
SCRIPT : 'script' ;
TRUE : 'true' ;
FALSE : 'false' ;
CALL : 'call' ;
REPEAT : 'repeat' ;
/*INT : 'int' ;
BOOL: 'bool' ;
TERMTYPE : 'term' ;*/
FOREACH : 'foreach' ;
THEONLY : 'theonly' ;
INDENT : '{' ;
DEDENT : '}' ;
SEMICOLON : ';' ;
COLON : ':' ;


STRING_LITERAL
   : '\'' ('\'\'' | ~ ('\''))* '\''
   ;

TERM_LITERAL
   : '`' ~('`')* '`'
   ;

PLUS : '+' ;
MINUS : '-' ;
MUL : '*' ;
DIV : '/' ;
EQ : '=' ;
NEQ : '!=' ;
GEQ : '>=' ;
LEQ : '<=' ;
GE : '>' ;
LE : '<' ;
AND : '&' ;
OR: '|' ;
IMP : '==>' ;
EQUIV : '<=>' ;
NOT: 'not';

EXE_MARKER: '\u2316' -> channel(HIDDEN);

DIGITS : DIGIT+ ;
fragment DIGIT : [0-9] ;
ID : [a-zA-Z] ([_a-zA-Z0-9] | '.' | '\\' | '[]')* ;
