grammar ScriptLanguage;


start
    :   script EOF
    ;


script
    : SCRIPT name=ID '(' signature=argList? ')' INDENT body=stmtList DEDENT
    | body=stmtList
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
    :
      casesStmt
    | scriptCommand
    | assignment
    ;

assignment
    :   variable=ID COLON type=ID SEMICOLON
    |   variable=ID (COLON type=ID)? ASSIGN expression SEMICOLON
    ;

expression
    :
        MINUS expression   #exprNegate
    |   NOT expression  #exprNot
   // |   expression LBRACKET substExpressionList RBRACKET  #exprSubst
    |   expression MUL expression #exprMultiplication
    |   <assoc=right> expression DIV expression #exprDivision
    |   expression op=(PLUS|MINUS) expression #exprLineOperators
    |   expression op=(LE|GE|LEQ|GEQ) expression #exprComparison
    |   expression op=(NEQ|EQ) expression  #exprEquality
    |   expression AND expression   #exprAnd
    |   expression OR expression    #exprOr
    |   expression IMP expression   #exprIMP
    |   '(' expression ')' #exprParen
    | literals             #exprLiterals
    | matchPattern         #exprMatch
;


/*substExpressionList
    :
    scriptVar '/' expression (',' substExpressionList)*
    ;
*/
literals :
        ID             #literalID
    |   DIGITS         #literalDigits
    |   TERM_LITERAL   #literalTerm
    |   MATCH_TERM_LITERAL #matchTermLiteral
    |   SEQUENT_LITERAL  #sequentLiteral
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


casesStmt
    :   CASES INDENT
            casesList*
        (DEFAULT  COLON INDENT?
            defList=stmtList
          DEDENT?)?
        DEDENT
    ;

casesList

    :   CASE  ( guard=expression| CLOSES INDENT closesScript=stmtList DEDENT) COLON INDENT? bodyScript=stmtList DEDENT?
    ;


parameters: parameter+;
parameter :  ((pname=ID '=')? expr=expression);

scriptCommand
    :   cmd=ID parameters? SEMICOLON
    ;

//LEXER Rules
WS : [ \t\n\r]+ -> channel(HIDDEN) ;

//comments, allowing nesting.
SINGLE_LINE_COMMENT : '//' ~[\r\n]* -> channel(HIDDEN);
MULTI_LINE_COMMENT  : '/*' (MULTI_LINE_COMMENT|.)*? '*/' -> channel(HIDDEN);
MULTI_LINE_COMMENT_BEGIN: '/*' ~('\n')* EOF -> channel(HIDDEN);

CASES: 'cases';
CASE: 'case';
CLOSES: 'closes';
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
SEQUENTSYMBOL : '|-';


STRING_LITERAL
  : '"' ( '\'' | ~('"')*) '"'
 //  : '\'' ('\'\'' | ~ ('\''))* '\''
   ;

SEQUENT_LITERAL
  : '\''  ~('\'')*  SEQUENTSYMBOL  ~('\'')* '\''
  ;

TERM_LITERAL
   : '\'' ~('\'')* '\''
   ;

MATCH_TERM_LITERAL
   : '\'\'' .*? '\'\''
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
ID : [a-zA-Z] ([_a-zA-Z0-9] | '.' | '\\' | LBRACKET RBRACKET ~('|' | '-'))* ;
