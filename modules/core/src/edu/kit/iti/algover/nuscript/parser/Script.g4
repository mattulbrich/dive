grammar Script;


script
    :   statement* EOF
    ;

statement
    :   casesStmt
    |   commandStmt
    ;

expression
    :   STRING_LITERAL
    |   TERM_LITERAL
    |   POSITION_LITERAL
    |   ID
    |   DIGITS
    |   TRUE | FALSE
    ;

casesStmt
    :   CASES BEGIN
            singleCase*
        END
    ;

singleCase
    :   label=STRING_LITERAL ':' statement*
    // | MATCH TERM_LITERAL ':' statement*  // later
    ;

commandStmt
    :   cmd=ID parameter* ';'
    ;

parameter
    :   (pname=ID '=')? expr=expression
    ;


BEGIN : '{';
CASES : 'cases';
END : '}';
MATCH : 'match';
TRUE : 'true';
FALSE : 'false';

DIGITS : [0-9]+;
ID : [a-zA-Z] ( [_a-zA-Z0-9] )*;
STRING_LITERAL : '"' ~('"')* '"';
TERM_LITERAL: '\'' ~('\'')* '\'';
POSITION_LITERAL: [SA] ( '.' [0-9]+ )+;

// LEXER Rules
WS : [ \t\n\r]+ -> channel(HIDDEN) ;

SINGLE_LINE_COMMENT : '//' ~[\r\n]* -> channel(HIDDEN);
MULTI_LINE_COMMENT  : '/*' (MULTI_LINE_COMMENT|.)*? '*/' -> channel(HIDDEN);
MULTI_LINE_COMMENT_BEGIN: '/*' ~('\n')* EOF -> channel(HIDDEN);
