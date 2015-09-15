// $ANTLR 3.5.1 Dafny.g 2015-09-11 12:18:36

  package edu.kit.iti.algover.parser;


import org.antlr.runtime.*;
import java.util.Stack;
import java.util.List;
import java.util.ArrayList;

@SuppressWarnings("all")
public class DafnyLexer extends Lexer {
	public static final int EOF=-1;
	public static final int T__53=53;
	public static final int T__54=54;
	public static final int T__55=55;
	public static final int T__56=56;
	public static final int T__57=57;
	public static final int T__58=58;
	public static final int T__59=59;
	public static final int ALL=4;
	public static final int AND=5;
	public static final int ARGS=6;
	public static final int ARRAY=7;
	public static final int ARRAY_ACCESS=8;
	public static final int ASSERT=9;
	public static final int ASSIGN=10;
	public static final int BLOCK=11;
	public static final int BLOCK_BEGIN=12;
	public static final int BLOCK_END=13;
	public static final int CALL=14;
	public static final int DECREASES=15;
	public static final int DOT=16;
	public static final int DOUBLECOLON=17;
	public static final int ELSE=18;
	public static final int ENSURES=19;
	public static final int EQ=20;
	public static final int EX=21;
	public static final int GE=22;
	public static final int GT=23;
	public static final int ID=24;
	public static final int IF=25;
	public static final int IMPLIES=26;
	public static final int INT=27;
	public static final int INTERSECT=28;
	public static final int INVARIANT=29;
	public static final int LABEL=30;
	public static final int LE=31;
	public static final int LEMMA=32;
	public static final int LENGTH=33;
	public static final int LISTEX=34;
	public static final int LIT=35;
	public static final int LT=36;
	public static final int METHOD=37;
	public static final int MINUS=38;
	public static final int NOT=39;
	public static final int OR=40;
	public static final int PLUS=41;
	public static final int REQUIRES=42;
	public static final int RESULTS=43;
	public static final int RETURNS=44;
	public static final int SET=45;
	public static final int SETEX=46;
	public static final int THEN=47;
	public static final int TIMES=48;
	public static final int UNION=49;
	public static final int VAR=50;
	public static final int WHILE=51;
	public static final int WS=52;

	// delegates
	// delegators
	public Lexer[] getDelegates() {
		return new Lexer[] {};
	}

	public DafnyLexer() {} 
	public DafnyLexer(CharStream input) {
		this(input, new RecognizerSharedState());
	}
	public DafnyLexer(CharStream input, RecognizerSharedState state) {
		super(input,state);
	}
	@Override public String getGrammarFileName() { return "Dafny.g"; }

	// $ANTLR start "T__53"
	public final void mT__53() throws RecognitionException {
		try {
			int _type = T__53;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// Dafny.g:6:7: ( '(' )
			// Dafny.g:6:9: '('
			{
			match('('); 
			}

			state.type = _type;
			state.channel = _channel;
		}
		finally {
			// do for sure before leaving
		}
	}
	// $ANTLR end "T__53"

	// $ANTLR start "T__54"
	public final void mT__54() throws RecognitionException {
		try {
			int _type = T__54;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// Dafny.g:7:7: ( ')' )
			// Dafny.g:7:9: ')'
			{
			match(')'); 
			}

			state.type = _type;
			state.channel = _channel;
		}
		finally {
			// do for sure before leaving
		}
	}
	// $ANTLR end "T__54"

	// $ANTLR start "T__55"
	public final void mT__55() throws RecognitionException {
		try {
			int _type = T__55;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// Dafny.g:8:7: ( ',' )
			// Dafny.g:8:9: ','
			{
			match(','); 
			}

			state.type = _type;
			state.channel = _channel;
		}
		finally {
			// do for sure before leaving
		}
	}
	// $ANTLR end "T__55"

	// $ANTLR start "T__56"
	public final void mT__56() throws RecognitionException {
		try {
			int _type = T__56;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// Dafny.g:9:7: ( ':' )
			// Dafny.g:9:9: ':'
			{
			match(':'); 
			}

			state.type = _type;
			state.channel = _channel;
		}
		finally {
			// do for sure before leaving
		}
	}
	// $ANTLR end "T__56"

	// $ANTLR start "T__57"
	public final void mT__57() throws RecognitionException {
		try {
			int _type = T__57;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// Dafny.g:10:7: ( ';' )
			// Dafny.g:10:9: ';'
			{
			match(';'); 
			}

			state.type = _type;
			state.channel = _channel;
		}
		finally {
			// do for sure before leaving
		}
	}
	// $ANTLR end "T__57"

	// $ANTLR start "T__58"
	public final void mT__58() throws RecognitionException {
		try {
			int _type = T__58;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// Dafny.g:11:7: ( '[' )
			// Dafny.g:11:9: '['
			{
			match('['); 
			}

			state.type = _type;
			state.channel = _channel;
		}
		finally {
			// do for sure before leaving
		}
	}
	// $ANTLR end "T__58"

	// $ANTLR start "T__59"
	public final void mT__59() throws RecognitionException {
		try {
			int _type = T__59;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// Dafny.g:12:7: ( ']' )
			// Dafny.g:12:9: ']'
			{
			match(']'); 
			}

			state.type = _type;
			state.channel = _channel;
		}
		finally {
			// do for sure before leaving
		}
	}
	// $ANTLR end "T__59"

	// $ANTLR start "INT"
	public final void mINT() throws RecognitionException {
		try {
			int _type = INT;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// Dafny.g:56:5: ( 'int' )
			// Dafny.g:56:7: 'int'
			{
			match("int"); 

			}

			state.type = _type;
			state.channel = _channel;
		}
		finally {
			// do for sure before leaving
		}
	}
	// $ANTLR end "INT"

	// $ANTLR start "SET"
	public final void mSET() throws RecognitionException {
		try {
			int _type = SET;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// Dafny.g:57:5: ( 'set' )
			// Dafny.g:57:7: 'set'
			{
			match("set"); 

			}

			state.type = _type;
			state.channel = _channel;
		}
		finally {
			// do for sure before leaving
		}
	}
	// $ANTLR end "SET"

	// $ANTLR start "RETURNS"
	public final void mRETURNS() throws RecognitionException {
		try {
			int _type = RETURNS;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// Dafny.g:58:9: ( 'returns' )
			// Dafny.g:58:11: 'returns'
			{
			match("returns"); 

			}

			state.type = _type;
			state.channel = _channel;
		}
		finally {
			// do for sure before leaving
		}
	}
	// $ANTLR end "RETURNS"

	// $ANTLR start "ENSURES"
	public final void mENSURES() throws RecognitionException {
		try {
			int _type = ENSURES;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// Dafny.g:59:8: ( 'ensures' )
			// Dafny.g:59:10: 'ensures'
			{
			match("ensures"); 

			}

			state.type = _type;
			state.channel = _channel;
		}
		finally {
			// do for sure before leaving
		}
	}
	// $ANTLR end "ENSURES"

	// $ANTLR start "REQUIRES"
	public final void mREQUIRES() throws RecognitionException {
		try {
			int _type = REQUIRES;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// Dafny.g:60:9: ( 'requires' )
			// Dafny.g:60:11: 'requires'
			{
			match("requires"); 

			}

			state.type = _type;
			state.channel = _channel;
		}
		finally {
			// do for sure before leaving
		}
	}
	// $ANTLR end "REQUIRES"

	// $ANTLR start "DECREASES"
	public final void mDECREASES() throws RecognitionException {
		try {
			int _type = DECREASES;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// Dafny.g:61:10: ( 'decreases' )
			// Dafny.g:61:12: 'decreases'
			{
			match("decreases"); 

			}

			state.type = _type;
			state.channel = _channel;
		}
		finally {
			// do for sure before leaving
		}
	}
	// $ANTLR end "DECREASES"

	// $ANTLR start "METHOD"
	public final void mMETHOD() throws RecognitionException {
		try {
			int _type = METHOD;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// Dafny.g:62:7: ( 'method' )
			// Dafny.g:62:9: 'method'
			{
			match("method"); 

			}

			state.type = _type;
			state.channel = _channel;
		}
		finally {
			// do for sure before leaving
		}
	}
	// $ANTLR end "METHOD"

	// $ANTLR start "LEMMA"
	public final void mLEMMA() throws RecognitionException {
		try {
			int _type = LEMMA;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// Dafny.g:63:6: ( 'lemma' )
			// Dafny.g:63:8: 'lemma'
			{
			match("lemma"); 

			}

			state.type = _type;
			state.channel = _channel;
		}
		finally {
			// do for sure before leaving
		}
	}
	// $ANTLR end "LEMMA"

	// $ANTLR start "LABEL"
	public final void mLABEL() throws RecognitionException {
		try {
			int _type = LABEL;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// Dafny.g:64:6: ( 'label' )
			// Dafny.g:64:8: 'label'
			{
			match("label"); 

			}

			state.type = _type;
			state.channel = _channel;
		}
		finally {
			// do for sure before leaving
		}
	}
	// $ANTLR end "LABEL"

	// $ANTLR start "ELSE"
	public final void mELSE() throws RecognitionException {
		try {
			int _type = ELSE;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// Dafny.g:65:5: ( 'else' )
			// Dafny.g:65:7: 'else'
			{
			match("else"); 

			}

			state.type = _type;
			state.channel = _channel;
		}
		finally {
			// do for sure before leaving
		}
	}
	// $ANTLR end "ELSE"

	// $ANTLR start "IF"
	public final void mIF() throws RecognitionException {
		try {
			int _type = IF;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// Dafny.g:66:3: ( 'if' )
			// Dafny.g:66:5: 'if'
			{
			match("if"); 

			}

			state.type = _type;
			state.channel = _channel;
		}
		finally {
			// do for sure before leaving
		}
	}
	// $ANTLR end "IF"

	// $ANTLR start "THEN"
	public final void mTHEN() throws RecognitionException {
		try {
			int _type = THEN;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// Dafny.g:67:5: ( 'then' )
			// Dafny.g:67:7: 'then'
			{
			match("then"); 

			}

			state.type = _type;
			state.channel = _channel;
		}
		finally {
			// do for sure before leaving
		}
	}
	// $ANTLR end "THEN"

	// $ANTLR start "WHILE"
	public final void mWHILE() throws RecognitionException {
		try {
			int _type = WHILE;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// Dafny.g:68:6: ( 'while' )
			// Dafny.g:68:8: 'while'
			{
			match("while"); 

			}

			state.type = _type;
			state.channel = _channel;
		}
		finally {
			// do for sure before leaving
		}
	}
	// $ANTLR end "WHILE"

	// $ANTLR start "VAR"
	public final void mVAR() throws RecognitionException {
		try {
			int _type = VAR;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// Dafny.g:69:4: ( 'var' )
			// Dafny.g:69:6: 'var'
			{
			match("var"); 

			}

			state.type = _type;
			state.channel = _channel;
		}
		finally {
			// do for sure before leaving
		}
	}
	// $ANTLR end "VAR"

	// $ANTLR start "CALL"
	public final void mCALL() throws RecognitionException {
		try {
			int _type = CALL;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// Dafny.g:70:5: ( 'call' )
			// Dafny.g:70:6: 'call'
			{
			match("call"); 

			}

			state.type = _type;
			state.channel = _channel;
		}
		finally {
			// do for sure before leaving
		}
	}
	// $ANTLR end "CALL"

	// $ANTLR start "INVARIANT"
	public final void mINVARIANT() throws RecognitionException {
		try {
			int _type = INVARIANT;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// Dafny.g:71:10: ( 'invariant' )
			// Dafny.g:71:12: 'invariant'
			{
			match("invariant"); 

			}

			state.type = _type;
			state.channel = _channel;
		}
		finally {
			// do for sure before leaving
		}
	}
	// $ANTLR end "INVARIANT"

	// $ANTLR start "ASSERT"
	public final void mASSERT() throws RecognitionException {
		try {
			int _type = ASSERT;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// Dafny.g:72:7: ( 'assert' )
			// Dafny.g:72:9: 'assert'
			{
			match("assert"); 

			}

			state.type = _type;
			state.channel = _channel;
		}
		finally {
			// do for sure before leaving
		}
	}
	// $ANTLR end "ASSERT"

	// $ANTLR start "ALL"
	public final void mALL() throws RecognitionException {
		try {
			int _type = ALL;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// Dafny.g:74:4: ( 'forall' )
			// Dafny.g:74:6: 'forall'
			{
			match("forall"); 

			}

			state.type = _type;
			state.channel = _channel;
		}
		finally {
			// do for sure before leaving
		}
	}
	// $ANTLR end "ALL"

	// $ANTLR start "EX"
	public final void mEX() throws RecognitionException {
		try {
			int _type = EX;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// Dafny.g:75:3: ( 'exists' )
			// Dafny.g:75:5: 'exists'
			{
			match("exists"); 

			}

			state.type = _type;
			state.channel = _channel;
		}
		finally {
			// do for sure before leaving
		}
	}
	// $ANTLR end "EX"

	// $ANTLR start "DOUBLECOLON"
	public final void mDOUBLECOLON() throws RecognitionException {
		try {
			int _type = DOUBLECOLON;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// Dafny.g:77:12: ( '::' )
			// Dafny.g:77:14: '::'
			{
			match("::"); 

			}

			state.type = _type;
			state.channel = _channel;
		}
		finally {
			// do for sure before leaving
		}
	}
	// $ANTLR end "DOUBLECOLON"

	// $ANTLR start "ASSIGN"
	public final void mASSIGN() throws RecognitionException {
		try {
			int _type = ASSIGN;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// Dafny.g:78:7: ( ':=' )
			// Dafny.g:78:9: ':='
			{
			match(":="); 

			}

			state.type = _type;
			state.channel = _channel;
		}
		finally {
			// do for sure before leaving
		}
	}
	// $ANTLR end "ASSIGN"

	// $ANTLR start "OR"
	public final void mOR() throws RecognitionException {
		try {
			int _type = OR;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// Dafny.g:79:3: ( '||' )
			// Dafny.g:79:5: '||'
			{
			match("||"); 

			}

			state.type = _type;
			state.channel = _channel;
		}
		finally {
			// do for sure before leaving
		}
	}
	// $ANTLR end "OR"

	// $ANTLR start "AND"
	public final void mAND() throws RecognitionException {
		try {
			int _type = AND;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// Dafny.g:80:4: ( '&&' )
			// Dafny.g:80:6: '&&'
			{
			match("&&"); 

			}

			state.type = _type;
			state.channel = _channel;
		}
		finally {
			// do for sure before leaving
		}
	}
	// $ANTLR end "AND"

	// $ANTLR start "IMPLIES"
	public final void mIMPLIES() throws RecognitionException {
		try {
			int _type = IMPLIES;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// Dafny.g:81:8: ( '==>' )
			// Dafny.g:81:10: '==>'
			{
			match("==>"); 

			}

			state.type = _type;
			state.channel = _channel;
		}
		finally {
			// do for sure before leaving
		}
	}
	// $ANTLR end "IMPLIES"

	// $ANTLR start "PLUS"
	public final void mPLUS() throws RecognitionException {
		try {
			int _type = PLUS;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// Dafny.g:82:5: ( '+' )
			// Dafny.g:82:7: '+'
			{
			match('+'); 
			}

			state.type = _type;
			state.channel = _channel;
		}
		finally {
			// do for sure before leaving
		}
	}
	// $ANTLR end "PLUS"

	// $ANTLR start "MINUS"
	public final void mMINUS() throws RecognitionException {
		try {
			int _type = MINUS;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// Dafny.g:83:6: ( '-' )
			// Dafny.g:83:8: '-'
			{
			match('-'); 
			}

			state.type = _type;
			state.channel = _channel;
		}
		finally {
			// do for sure before leaving
		}
	}
	// $ANTLR end "MINUS"

	// $ANTLR start "NOT"
	public final void mNOT() throws RecognitionException {
		try {
			int _type = NOT;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// Dafny.g:84:4: ( '!' )
			// Dafny.g:84:6: '!'
			{
			match('!'); 
			}

			state.type = _type;
			state.channel = _channel;
		}
		finally {
			// do for sure before leaving
		}
	}
	// $ANTLR end "NOT"

	// $ANTLR start "TIMES"
	public final void mTIMES() throws RecognitionException {
		try {
			int _type = TIMES;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// Dafny.g:85:6: ( '*' )
			// Dafny.g:85:8: '*'
			{
			match('*'); 
			}

			state.type = _type;
			state.channel = _channel;
		}
		finally {
			// do for sure before leaving
		}
	}
	// $ANTLR end "TIMES"

	// $ANTLR start "UNION"
	public final void mUNION() throws RecognitionException {
		try {
			int _type = UNION;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// Dafny.g:86:6: ( '++' )
			// Dafny.g:86:8: '++'
			{
			match("++"); 

			}

			state.type = _type;
			state.channel = _channel;
		}
		finally {
			// do for sure before leaving
		}
	}
	// $ANTLR end "UNION"

	// $ANTLR start "INTERSECT"
	public final void mINTERSECT() throws RecognitionException {
		try {
			int _type = INTERSECT;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// Dafny.g:87:10: ( '**' )
			// Dafny.g:87:12: '**'
			{
			match("**"); 

			}

			state.type = _type;
			state.channel = _channel;
		}
		finally {
			// do for sure before leaving
		}
	}
	// $ANTLR end "INTERSECT"

	// $ANTLR start "LT"
	public final void mLT() throws RecognitionException {
		try {
			int _type = LT;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// Dafny.g:88:3: ( '<' )
			// Dafny.g:88:5: '<'
			{
			match('<'); 
			}

			state.type = _type;
			state.channel = _channel;
		}
		finally {
			// do for sure before leaving
		}
	}
	// $ANTLR end "LT"

	// $ANTLR start "LE"
	public final void mLE() throws RecognitionException {
		try {
			int _type = LE;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// Dafny.g:89:3: ( '<=' )
			// Dafny.g:89:5: '<='
			{
			match("<="); 

			}

			state.type = _type;
			state.channel = _channel;
		}
		finally {
			// do for sure before leaving
		}
	}
	// $ANTLR end "LE"

	// $ANTLR start "GT"
	public final void mGT() throws RecognitionException {
		try {
			int _type = GT;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// Dafny.g:90:3: ( '>' )
			// Dafny.g:90:5: '>'
			{
			match('>'); 
			}

			state.type = _type;
			state.channel = _channel;
		}
		finally {
			// do for sure before leaving
		}
	}
	// $ANTLR end "GT"

	// $ANTLR start "GE"
	public final void mGE() throws RecognitionException {
		try {
			int _type = GE;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// Dafny.g:91:3: ( '>=' )
			// Dafny.g:91:5: '>='
			{
			match(">="); 

			}

			state.type = _type;
			state.channel = _channel;
		}
		finally {
			// do for sure before leaving
		}
	}
	// $ANTLR end "GE"

	// $ANTLR start "EQ"
	public final void mEQ() throws RecognitionException {
		try {
			int _type = EQ;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// Dafny.g:92:3: ( '==' )
			// Dafny.g:92:5: '=='
			{
			match("=="); 

			}

			state.type = _type;
			state.channel = _channel;
		}
		finally {
			// do for sure before leaving
		}
	}
	// $ANTLR end "EQ"

	// $ANTLR start "DOT"
	public final void mDOT() throws RecognitionException {
		try {
			int _type = DOT;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// Dafny.g:93:4: ( '.' )
			// Dafny.g:93:6: '.'
			{
			match('.'); 
			}

			state.type = _type;
			state.channel = _channel;
		}
		finally {
			// do for sure before leaving
		}
	}
	// $ANTLR end "DOT"

	// $ANTLR start "BLOCK_BEGIN"
	public final void mBLOCK_BEGIN() throws RecognitionException {
		try {
			int _type = BLOCK_BEGIN;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// Dafny.g:94:12: ( '{' )
			// Dafny.g:94:14: '{'
			{
			match('{'); 
			}

			state.type = _type;
			state.channel = _channel;
		}
		finally {
			// do for sure before leaving
		}
	}
	// $ANTLR end "BLOCK_BEGIN"

	// $ANTLR start "BLOCK_END"
	public final void mBLOCK_END() throws RecognitionException {
		try {
			int _type = BLOCK_END;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// Dafny.g:95:10: ( '}' )
			// Dafny.g:95:12: '}'
			{
			match('}'); 
			}

			state.type = _type;
			state.channel = _channel;
		}
		finally {
			// do for sure before leaving
		}
	}
	// $ANTLR end "BLOCK_END"

	// $ANTLR start "LENGTH"
	public final void mLENGTH() throws RecognitionException {
		try {
			int _type = LENGTH;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// Dafny.g:97:7: ( 'Length' ( '0' .. '9' )* )
			// Dafny.g:97:9: 'Length' ( '0' .. '9' )*
			{
			match("Length"); 

			// Dafny.g:97:18: ( '0' .. '9' )*
			loop1:
			while (true) {
				int alt1=2;
				int LA1_0 = input.LA(1);
				if ( ((LA1_0 >= '0' && LA1_0 <= '9')) ) {
					alt1=1;
				}

				switch (alt1) {
				case 1 :
					// Dafny.g:
					{
					if ( (input.LA(1) >= '0' && input.LA(1) <= '9') ) {
						input.consume();
					}
					else {
						MismatchedSetException mse = new MismatchedSetException(null,input);
						recover(mse);
						throw mse;
					}
					}
					break;

				default :
					break loop1;
				}
			}

			}

			state.type = _type;
			state.channel = _channel;
		}
		finally {
			// do for sure before leaving
		}
	}
	// $ANTLR end "LENGTH"

	// $ANTLR start "ARRAY"
	public final void mARRAY() throws RecognitionException {
		try {
			int _type = ARRAY;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// Dafny.g:98:7: ( 'array' ( ( '1' .. '9' ) ( '0' .. '9' )* )? )
			// Dafny.g:98:9: 'array' ( ( '1' .. '9' ) ( '0' .. '9' )* )?
			{
			match("array"); 

			// Dafny.g:98:17: ( ( '1' .. '9' ) ( '0' .. '9' )* )?
			int alt3=2;
			int LA3_0 = input.LA(1);
			if ( ((LA3_0 >= '1' && LA3_0 <= '9')) ) {
				alt3=1;
			}
			switch (alt3) {
				case 1 :
					// Dafny.g:98:18: ( '1' .. '9' ) ( '0' .. '9' )*
					{
					if ( (input.LA(1) >= '1' && input.LA(1) <= '9') ) {
						input.consume();
					}
					else {
						MismatchedSetException mse = new MismatchedSetException(null,input);
						recover(mse);
						throw mse;
					}
					// Dafny.g:98:31: ( '0' .. '9' )*
					loop2:
					while (true) {
						int alt2=2;
						int LA2_0 = input.LA(1);
						if ( ((LA2_0 >= '0' && LA2_0 <= '9')) ) {
							alt2=1;
						}

						switch (alt2) {
						case 1 :
							// Dafny.g:
							{
							if ( (input.LA(1) >= '0' && input.LA(1) <= '9') ) {
								input.consume();
							}
							else {
								MismatchedSetException mse = new MismatchedSetException(null,input);
								recover(mse);
								throw mse;
							}
							}
							break;

						default :
							break loop2;
						}
					}

					}
					break;

			}

			}

			state.type = _type;
			state.channel = _channel;
		}
		finally {
			// do for sure before leaving
		}
	}
	// $ANTLR end "ARRAY"

	// $ANTLR start "ID"
	public final void mID() throws RecognitionException {
		try {
			int _type = ID;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// Dafny.g:99:4: ( ( 'a' .. 'z' | 'A' .. 'Z' | '_' )+ )
			// Dafny.g:99:6: ( 'a' .. 'z' | 'A' .. 'Z' | '_' )+
			{
			// Dafny.g:99:6: ( 'a' .. 'z' | 'A' .. 'Z' | '_' )+
			int cnt4=0;
			loop4:
			while (true) {
				int alt4=2;
				int LA4_0 = input.LA(1);
				if ( ((LA4_0 >= 'A' && LA4_0 <= 'Z')||LA4_0=='_'||(LA4_0 >= 'a' && LA4_0 <= 'z')) ) {
					alt4=1;
				}

				switch (alt4) {
				case 1 :
					// Dafny.g:
					{
					if ( (input.LA(1) >= 'A' && input.LA(1) <= 'Z')||input.LA(1)=='_'||(input.LA(1) >= 'a' && input.LA(1) <= 'z') ) {
						input.consume();
					}
					else {
						MismatchedSetException mse = new MismatchedSetException(null,input);
						recover(mse);
						throw mse;
					}
					}
					break;

				default :
					if ( cnt4 >= 1 ) break loop4;
					EarlyExitException eee = new EarlyExitException(4, input);
					throw eee;
				}
				cnt4++;
			}

			}

			state.type = _type;
			state.channel = _channel;
		}
		finally {
			// do for sure before leaving
		}
	}
	// $ANTLR end "ID"

	// $ANTLR start "LIT"
	public final void mLIT() throws RecognitionException {
		try {
			int _type = LIT;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// Dafny.g:100:5: ( ( '0' .. '9' )+ )
			// Dafny.g:100:7: ( '0' .. '9' )+
			{
			// Dafny.g:100:7: ( '0' .. '9' )+
			int cnt5=0;
			loop5:
			while (true) {
				int alt5=2;
				int LA5_0 = input.LA(1);
				if ( ((LA5_0 >= '0' && LA5_0 <= '9')) ) {
					alt5=1;
				}

				switch (alt5) {
				case 1 :
					// Dafny.g:
					{
					if ( (input.LA(1) >= '0' && input.LA(1) <= '9') ) {
						input.consume();
					}
					else {
						MismatchedSetException mse = new MismatchedSetException(null,input);
						recover(mse);
						throw mse;
					}
					}
					break;

				default :
					if ( cnt5 >= 1 ) break loop5;
					EarlyExitException eee = new EarlyExitException(5, input);
					throw eee;
				}
				cnt5++;
			}

			}

			state.type = _type;
			state.channel = _channel;
		}
		finally {
			// do for sure before leaving
		}
	}
	// $ANTLR end "LIT"

	// $ANTLR start "WS"
	public final void mWS() throws RecognitionException {
		try {
			int _type = WS;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// Dafny.g:101:4: ( ( ' ' | '\\n' | '\\r' ) )
			// Dafny.g:101:6: ( ' ' | '\\n' | '\\r' )
			{
			if ( input.LA(1)=='\n'||input.LA(1)=='\r'||input.LA(1)==' ' ) {
				input.consume();
			}
			else {
				MismatchedSetException mse = new MismatchedSetException(null,input);
				recover(mse);
				throw mse;
			}
			 _channel = HIDDEN; 
			}

			state.type = _type;
			state.channel = _channel;
		}
		finally {
			// do for sure before leaving
		}
	}
	// $ANTLR end "WS"

	@Override
	public void mTokens() throws RecognitionException {
		// Dafny.g:1:8: ( T__53 | T__54 | T__55 | T__56 | T__57 | T__58 | T__59 | INT | SET | RETURNS | ENSURES | REQUIRES | DECREASES | METHOD | LEMMA | LABEL | ELSE | IF | THEN | WHILE | VAR | CALL | INVARIANT | ASSERT | ALL | EX | DOUBLECOLON | ASSIGN | OR | AND | IMPLIES | PLUS | MINUS | NOT | TIMES | UNION | INTERSECT | LT | LE | GT | GE | EQ | DOT | BLOCK_BEGIN | BLOCK_END | LENGTH | ARRAY | ID | LIT | WS )
		int alt6=50;
		alt6 = dfa6.predict(input);
		switch (alt6) {
			case 1 :
				// Dafny.g:1:10: T__53
				{
				mT__53(); 

				}
				break;
			case 2 :
				// Dafny.g:1:16: T__54
				{
				mT__54(); 

				}
				break;
			case 3 :
				// Dafny.g:1:22: T__55
				{
				mT__55(); 

				}
				break;
			case 4 :
				// Dafny.g:1:28: T__56
				{
				mT__56(); 

				}
				break;
			case 5 :
				// Dafny.g:1:34: T__57
				{
				mT__57(); 

				}
				break;
			case 6 :
				// Dafny.g:1:40: T__58
				{
				mT__58(); 

				}
				break;
			case 7 :
				// Dafny.g:1:46: T__59
				{
				mT__59(); 

				}
				break;
			case 8 :
				// Dafny.g:1:52: INT
				{
				mINT(); 

				}
				break;
			case 9 :
				// Dafny.g:1:56: SET
				{
				mSET(); 

				}
				break;
			case 10 :
				// Dafny.g:1:60: RETURNS
				{
				mRETURNS(); 

				}
				break;
			case 11 :
				// Dafny.g:1:68: ENSURES
				{
				mENSURES(); 

				}
				break;
			case 12 :
				// Dafny.g:1:76: REQUIRES
				{
				mREQUIRES(); 

				}
				break;
			case 13 :
				// Dafny.g:1:85: DECREASES
				{
				mDECREASES(); 

				}
				break;
			case 14 :
				// Dafny.g:1:95: METHOD
				{
				mMETHOD(); 

				}
				break;
			case 15 :
				// Dafny.g:1:102: LEMMA
				{
				mLEMMA(); 

				}
				break;
			case 16 :
				// Dafny.g:1:108: LABEL
				{
				mLABEL(); 

				}
				break;
			case 17 :
				// Dafny.g:1:114: ELSE
				{
				mELSE(); 

				}
				break;
			case 18 :
				// Dafny.g:1:119: IF
				{
				mIF(); 

				}
				break;
			case 19 :
				// Dafny.g:1:122: THEN
				{
				mTHEN(); 

				}
				break;
			case 20 :
				// Dafny.g:1:127: WHILE
				{
				mWHILE(); 

				}
				break;
			case 21 :
				// Dafny.g:1:133: VAR
				{
				mVAR(); 

				}
				break;
			case 22 :
				// Dafny.g:1:137: CALL
				{
				mCALL(); 

				}
				break;
			case 23 :
				// Dafny.g:1:142: INVARIANT
				{
				mINVARIANT(); 

				}
				break;
			case 24 :
				// Dafny.g:1:152: ASSERT
				{
				mASSERT(); 

				}
				break;
			case 25 :
				// Dafny.g:1:159: ALL
				{
				mALL(); 

				}
				break;
			case 26 :
				// Dafny.g:1:163: EX
				{
				mEX(); 

				}
				break;
			case 27 :
				// Dafny.g:1:166: DOUBLECOLON
				{
				mDOUBLECOLON(); 

				}
				break;
			case 28 :
				// Dafny.g:1:178: ASSIGN
				{
				mASSIGN(); 

				}
				break;
			case 29 :
				// Dafny.g:1:185: OR
				{
				mOR(); 

				}
				break;
			case 30 :
				// Dafny.g:1:188: AND
				{
				mAND(); 

				}
				break;
			case 31 :
				// Dafny.g:1:192: IMPLIES
				{
				mIMPLIES(); 

				}
				break;
			case 32 :
				// Dafny.g:1:200: PLUS
				{
				mPLUS(); 

				}
				break;
			case 33 :
				// Dafny.g:1:205: MINUS
				{
				mMINUS(); 

				}
				break;
			case 34 :
				// Dafny.g:1:211: NOT
				{
				mNOT(); 

				}
				break;
			case 35 :
				// Dafny.g:1:215: TIMES
				{
				mTIMES(); 

				}
				break;
			case 36 :
				// Dafny.g:1:221: UNION
				{
				mUNION(); 

				}
				break;
			case 37 :
				// Dafny.g:1:227: INTERSECT
				{
				mINTERSECT(); 

				}
				break;
			case 38 :
				// Dafny.g:1:237: LT
				{
				mLT(); 

				}
				break;
			case 39 :
				// Dafny.g:1:240: LE
				{
				mLE(); 

				}
				break;
			case 40 :
				// Dafny.g:1:243: GT
				{
				mGT(); 

				}
				break;
			case 41 :
				// Dafny.g:1:246: GE
				{
				mGE(); 

				}
				break;
			case 42 :
				// Dafny.g:1:249: EQ
				{
				mEQ(); 

				}
				break;
			case 43 :
				// Dafny.g:1:252: DOT
				{
				mDOT(); 

				}
				break;
			case 44 :
				// Dafny.g:1:256: BLOCK_BEGIN
				{
				mBLOCK_BEGIN(); 

				}
				break;
			case 45 :
				// Dafny.g:1:268: BLOCK_END
				{
				mBLOCK_END(); 

				}
				break;
			case 46 :
				// Dafny.g:1:278: LENGTH
				{
				mLENGTH(); 

				}
				break;
			case 47 :
				// Dafny.g:1:285: ARRAY
				{
				mARRAY(); 

				}
				break;
			case 48 :
				// Dafny.g:1:291: ID
				{
				mID(); 

				}
				break;
			case 49 :
				// Dafny.g:1:294: LIT
				{
				mLIT(); 

				}
				break;
			case 50 :
				// Dafny.g:1:298: WS
				{
				mWS(); 

				}
				break;

		}
	}


	protected DFA6 dfa6 = new DFA6(this);
	static final String DFA6_eotS =
		"\4\uffff\1\47\3\uffff\15\42\3\uffff\1\74\2\uffff\1\76\1\100\1\102\3\uffff"+
		"\1\42\6\uffff\1\42\1\106\20\42\1\131\10\uffff\1\42\1\133\1\42\1\uffff"+
		"\1\135\13\42\1\151\4\42\2\uffff\1\42\1\uffff\1\42\1\uffff\3\42\1\163\5"+
		"\42\1\171\1\42\1\uffff\1\173\10\42\1\uffff\3\42\1\u0087\1\u0088\1\uffff"+
		"\1\u0089\1\uffff\1\42\1\u008b\6\42\1\u0092\1\42\1\u0094\3\uffff\1\u0095"+
		"\1\uffff\1\u0096\1\u0097\1\42\1\u0099\1\42\1\u009b\1\uffff\1\42\4\uffff"+
		"\1\42\1\uffff\1\u009e\1\uffff\1\42\1\u00a0\1\uffff\1\u00a1\2\uffff";
	static final String DFA6_eofS =
		"\u00a2\uffff";
	static final String DFA6_minS =
		"\1\12\3\uffff\1\72\3\uffff\1\146\2\145\1\154\2\145\1\141\2\150\2\141\1"+
		"\162\1\157\2\uffff\1\75\1\53\2\uffff\1\52\2\75\3\uffff\1\145\6\uffff\1"+
		"\164\1\101\1\164\1\161\2\163\1\151\1\143\1\164\1\155\1\142\1\145\1\151"+
		"\1\162\1\154\1\163\2\162\1\76\10\uffff\1\156\1\101\1\141\1\uffff\1\101"+
		"\3\165\1\145\1\163\1\162\1\150\1\155\1\145\1\156\1\154\1\101\1\154\1\145"+
		"\2\141\2\uffff\1\147\1\uffff\1\162\1\uffff\1\162\1\151\1\162\1\101\1\164"+
		"\1\145\1\157\1\141\1\154\1\101\1\145\1\uffff\1\101\1\162\1\171\1\154\1"+
		"\164\1\151\1\156\1\162\1\145\1\uffff\1\163\1\141\1\144\2\101\1\uffff\1"+
		"\101\1\uffff\1\164\1\101\1\154\1\150\1\141\1\163\1\145\1\163\1\101\1\163"+
		"\1\101\3\uffff\1\101\1\uffff\2\101\1\156\1\101\1\163\1\101\1\uffff\1\145"+
		"\4\uffff\1\164\1\uffff\1\101\1\uffff\1\163\1\101\1\uffff\1\101\2\uffff";
	static final String DFA6_maxS =
		"\1\175\3\uffff\1\75\3\uffff\1\156\2\145\1\170\3\145\2\150\2\141\1\163"+
		"\1\157\2\uffff\1\75\1\53\2\uffff\1\52\2\75\3\uffff\1\145\6\uffff\1\166"+
		"\1\172\2\164\2\163\1\151\1\143\1\164\1\155\1\142\1\145\1\151\1\162\1\154"+
		"\1\163\2\162\1\76\10\uffff\1\156\1\172\1\141\1\uffff\1\172\3\165\1\145"+
		"\1\163\1\162\1\150\1\155\1\145\1\156\1\154\1\172\1\154\1\145\2\141\2\uffff"+
		"\1\147\1\uffff\1\162\1\uffff\1\162\1\151\1\162\1\172\1\164\1\145\1\157"+
		"\1\141\1\154\1\172\1\145\1\uffff\1\172\1\162\1\171\1\154\1\164\1\151\1"+
		"\156\1\162\1\145\1\uffff\1\163\1\141\1\144\2\172\1\uffff\1\172\1\uffff"+
		"\1\164\1\172\1\154\1\150\1\141\1\163\1\145\1\163\1\172\1\163\1\172\3\uffff"+
		"\1\172\1\uffff\2\172\1\156\1\172\1\163\1\172\1\uffff\1\145\4\uffff\1\164"+
		"\1\uffff\1\172\1\uffff\1\163\1\172\1\uffff\1\172\2\uffff";
	static final String DFA6_acceptS =
		"\1\uffff\1\1\1\2\1\3\1\uffff\1\5\1\6\1\7\15\uffff\1\35\1\36\2\uffff\1"+
		"\41\1\42\3\uffff\1\53\1\54\1\55\1\uffff\1\60\1\61\1\62\1\33\1\34\1\4\23"+
		"\uffff\1\44\1\40\1\45\1\43\1\47\1\46\1\51\1\50\3\uffff\1\22\21\uffff\1"+
		"\37\1\52\1\uffff\1\10\1\uffff\1\11\13\uffff\1\25\11\uffff\1\21\5\uffff"+
		"\1\23\1\uffff\1\26\13\uffff\1\17\1\20\1\24\1\uffff\1\57\6\uffff\1\32\1"+
		"\uffff\1\16\1\30\1\31\1\56\1\uffff\1\12\1\uffff\1\13\2\uffff\1\14\1\uffff"+
		"\1\27\1\15";
	static final String DFA6_specialS =
		"\u00a2\uffff}>";
	static final String[] DFA6_transitionS = {
			"\1\44\2\uffff\1\44\22\uffff\1\44\1\32\4\uffff\1\26\1\uffff\1\1\1\2\1"+
			"\33\1\30\1\3\1\31\1\36\1\uffff\12\43\1\4\1\5\1\34\1\27\1\35\2\uffff\13"+
			"\42\1\41\16\42\1\6\1\uffff\1\7\1\uffff\1\42\1\uffff\1\23\1\42\1\22\1"+
			"\14\1\13\1\24\2\42\1\10\2\42\1\16\1\15\4\42\1\12\1\11\1\17\1\42\1\21"+
			"\1\20\3\42\1\37\1\25\1\40",
			"",
			"",
			"",
			"\1\45\2\uffff\1\46",
			"",
			"",
			"",
			"\1\51\7\uffff\1\50",
			"\1\52",
			"\1\53",
			"\1\55\1\uffff\1\54\11\uffff\1\56",
			"\1\57",
			"\1\60",
			"\1\62\3\uffff\1\61",
			"\1\63",
			"\1\64",
			"\1\65",
			"\1\66",
			"\1\70\1\67",
			"\1\71",
			"",
			"",
			"\1\72",
			"\1\73",
			"",
			"",
			"\1\75",
			"\1\77",
			"\1\101",
			"",
			"",
			"",
			"\1\103",
			"",
			"",
			"",
			"",
			"",
			"",
			"\1\104\1\uffff\1\105",
			"\32\42\4\uffff\1\42\1\uffff\32\42",
			"\1\107",
			"\1\111\2\uffff\1\110",
			"\1\112",
			"\1\113",
			"\1\114",
			"\1\115",
			"\1\116",
			"\1\117",
			"\1\120",
			"\1\121",
			"\1\122",
			"\1\123",
			"\1\124",
			"\1\125",
			"\1\126",
			"\1\127",
			"\1\130",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"\1\132",
			"\32\42\4\uffff\1\42\1\uffff\32\42",
			"\1\134",
			"",
			"\32\42\4\uffff\1\42\1\uffff\32\42",
			"\1\136",
			"\1\137",
			"\1\140",
			"\1\141",
			"\1\142",
			"\1\143",
			"\1\144",
			"\1\145",
			"\1\146",
			"\1\147",
			"\1\150",
			"\32\42\4\uffff\1\42\1\uffff\32\42",
			"\1\152",
			"\1\153",
			"\1\154",
			"\1\155",
			"",
			"",
			"\1\156",
			"",
			"\1\157",
			"",
			"\1\160",
			"\1\161",
			"\1\162",
			"\32\42\4\uffff\1\42\1\uffff\32\42",
			"\1\164",
			"\1\165",
			"\1\166",
			"\1\167",
			"\1\170",
			"\32\42\4\uffff\1\42\1\uffff\32\42",
			"\1\172",
			"",
			"\32\42\4\uffff\1\42\1\uffff\32\42",
			"\1\174",
			"\1\175",
			"\1\176",
			"\1\177",
			"\1\u0080",
			"\1\u0081",
			"\1\u0082",
			"\1\u0083",
			"",
			"\1\u0084",
			"\1\u0085",
			"\1\u0086",
			"\32\42\4\uffff\1\42\1\uffff\32\42",
			"\32\42\4\uffff\1\42\1\uffff\32\42",
			"",
			"\32\42\4\uffff\1\42\1\uffff\32\42",
			"",
			"\1\u008a",
			"\32\42\4\uffff\1\42\1\uffff\32\42",
			"\1\u008c",
			"\1\u008d",
			"\1\u008e",
			"\1\u008f",
			"\1\u0090",
			"\1\u0091",
			"\32\42\4\uffff\1\42\1\uffff\32\42",
			"\1\u0093",
			"\32\42\4\uffff\1\42\1\uffff\32\42",
			"",
			"",
			"",
			"\32\42\4\uffff\1\42\1\uffff\32\42",
			"",
			"\32\42\4\uffff\1\42\1\uffff\32\42",
			"\32\42\4\uffff\1\42\1\uffff\32\42",
			"\1\u0098",
			"\32\42\4\uffff\1\42\1\uffff\32\42",
			"\1\u009a",
			"\32\42\4\uffff\1\42\1\uffff\32\42",
			"",
			"\1\u009c",
			"",
			"",
			"",
			"",
			"\1\u009d",
			"",
			"\32\42\4\uffff\1\42\1\uffff\32\42",
			"",
			"\1\u009f",
			"\32\42\4\uffff\1\42\1\uffff\32\42",
			"",
			"\32\42\4\uffff\1\42\1\uffff\32\42",
			"",
			""
	};

	static final short[] DFA6_eot = DFA.unpackEncodedString(DFA6_eotS);
	static final short[] DFA6_eof = DFA.unpackEncodedString(DFA6_eofS);
	static final char[] DFA6_min = DFA.unpackEncodedStringToUnsignedChars(DFA6_minS);
	static final char[] DFA6_max = DFA.unpackEncodedStringToUnsignedChars(DFA6_maxS);
	static final short[] DFA6_accept = DFA.unpackEncodedString(DFA6_acceptS);
	static final short[] DFA6_special = DFA.unpackEncodedString(DFA6_specialS);
	static final short[][] DFA6_transition;

	static {
		int numStates = DFA6_transitionS.length;
		DFA6_transition = new short[numStates][];
		for (int i=0; i<numStates; i++) {
			DFA6_transition[i] = DFA.unpackEncodedString(DFA6_transitionS[i]);
		}
	}

	protected class DFA6 extends DFA {

		public DFA6(BaseRecognizer recognizer) {
			this.recognizer = recognizer;
			this.decisionNumber = 6;
			this.eot = DFA6_eot;
			this.eof = DFA6_eof;
			this.min = DFA6_min;
			this.max = DFA6_max;
			this.accept = DFA6_accept;
			this.special = DFA6_special;
			this.transition = DFA6_transition;
		}
		@Override
		public String getDescription() {
			return "1:1: Tokens : ( T__53 | T__54 | T__55 | T__56 | T__57 | T__58 | T__59 | INT | SET | RETURNS | ENSURES | REQUIRES | DECREASES | METHOD | LEMMA | LABEL | ELSE | IF | THEN | WHILE | VAR | CALL | INVARIANT | ASSERT | ALL | EX | DOUBLECOLON | ASSIGN | OR | AND | IMPLIES | PLUS | MINUS | NOT | TIMES | UNION | INTERSECT | LT | LE | GT | GE | EQ | DOT | BLOCK_BEGIN | BLOCK_END | LENGTH | ARRAY | ID | LIT | WS );";
		}
	}

}
