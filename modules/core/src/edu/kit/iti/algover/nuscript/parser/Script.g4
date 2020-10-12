grammar Script;

/**
 * A new simplified parser for DIVE scripts.
 *
 * @author Mattias Ulbrich
 */

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
    |   SELECTOR_LITERAL
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
    :   CASE? ( MATCH { System.err.println("'case match' is deprecated and will be removed. Drop the match. Or both.");} )?
          label=STRING_LITERAL ':'
          ( statement* | BEGIN statement* END
          { System.err.println("'{ ... }' for cases is deprecated and will be removed. Drop the braces.");})
    // | MATCH TERM_LITERAL ':' statement*  // later
    ;

commandStmt
    :   cmd=ID parameter* ';'
    ;

parameter
    :   (pname=ID '=')? expr=expression
    ;


BEGIN : '{';
CASE : 'case';
CASES : 'cases';
END : '}';
MATCH : 'match';
TRUE : 'true';
FALSE : 'false';

DIGITS : [0-9]+;
ID : [a-zA-Z] ( [_a-zA-Z0-9] )*;
STRING_LITERAL : '"' ~('"')* '"';
TERM_LITERAL: '\'' ~('\'')* '\'';
SELECTOR_LITERAL: [SA] ( '.' [0-9]+ )+;

// LEXER Rules
WS : [ \t\n\r]+ -> channel(HIDDEN) ;

SINGLE_LINE_COMMENT : '//' ~[\r\n]* -> channel(HIDDEN);
MULTI_LINE_COMMENT  : '/*' (MULTI_LINE_COMMENT|.)*? '*/' -> channel(HIDDEN);
MULTI_LINE_COMMENT_BEGIN: '/*' ~('\n')* EOF -> channel(HIDDEN);

UNKNOWN_CHARACTER : . ;
