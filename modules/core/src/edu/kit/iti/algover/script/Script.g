grammar Script;

options {
  output = AST;
  ASTLabelType=ScriptTree;
}

tokens {

}

@parser::header {
  package edu.kit.iti.algover.script;
}

@lexer::header {
  package edu.kit.iti.algover.script;
}


IMPORT: 'import';
LIBRARY: 'lib';
PREAMBLE: 'preamble';
SETTINGS: 'settings';
BEGIN: 'begin';
END: 'end';
TIMEOUT: 'timeout';
TRUE: 'true';
FALSE: 'false';
LOOPUNROLL: 'loopunrolling';
INLINE: 'inline methods';
DAFNYEND:'.dfy' ;
FILE: 'file';
SUBSCRIPT: 'script for';
PVC	: 'PVC';
SET	:	'set';
APPLY: 'apply';
VCG: 'VCG';
POSTPONE: 'postpone';
PROOF:'Proof';
QED: 'Qed';
KEYTIMEOUT: 'key_timeout';
DAFNYTIMEOUT:'dafny_timeout';

ID : ('a' .. 'z' | 'A' .. 'Z' | '_') ('a' .. 'z' | 'A' .. 'Z' | '0' .. '9' | '_')*;
INT : ('0' .. '9' ) ('0' .. '9')*;
PATHSEP	:	'/'|'..'|'.';

WS : (' '|'\n'|'\r')                     { $channel = HIDDEN; };
SINGLELINE_COMMENT: '//' ~('\r' | '\n')* { $channel = HIDDEN; };
MULTILINE_COMMENT: '/*' .* '*/'          { $channel = HIDDEN; };

preamble:
  PREAMBLE BEGIN! ( importDafny ';'! |  importLibs ';'! | sets )+ END! pvcscripts* EOF
  ;

importDafny:
  IMPORT^ dafnyfiles
  ;

importLibs:
  LIBRARY^ dafnyfiles
  ;

dafnyfiles:
  dafnyfile (','! dafnyfiles)*
  ;

// REVIEW MU: Is this a lexer or a parser rule?
// If parser rule. Are whitespaces not overread?
file:
  (PATHSEP)*ID+(ID|INT|PATHSEP)* 
  ;

dafnyfile:
  file DAFNYEND
    -> ^(FILE file DAFNYEND)
  ;

sets:
  SETTINGS^ set (set)*;

// REVIEW MU: Why INT+ ?
set:
  '[' (tok=(DAFNYTIMEOUT|KEYTIMEOUT)) ']' INT+ ';'
    -> ^(SET [tok] INT+)
  ;

pvcscripts:
  pvcscript (pvcscripts)*
  ;

pvcscript:
  SUBSCRIPT^ pvc ':' '{' commands* QED? '}'
  ;

pvc:
  'PVC_' INT+
  ;

branchingcommand:
  ID+ ';'
  '{' commands+ '}'
  '{' commands+ '}'
  ;

commands:
  command | branchingcommand
  ;

command	:
  ID+ ';'
  ;