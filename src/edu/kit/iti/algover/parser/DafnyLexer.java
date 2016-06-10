// $ANTLR 3.5.1 Dafny.g 2016-06-10 09:23:40

  package edu.kit.iti.algover.parser;


import org.antlr.runtime.*;
import java.util.Stack;
import java.util.List;
import java.util.ArrayList;

@SuppressWarnings("all")
public class DafnyLexer extends Lexer {
	public static final int EOF=-1;
	public static final int T__59=59;
	public static final int T__60=60;
	public static final int T__61=61;
	public static final int T__62=62;
	public static final int T__63=63;
	public static final int T__64=64;
	public static final int T__65=65;
	public static final int ALL=4;
	public static final int AND=5;
	public static final int ARGS=6;
	public static final int ARRAY=7;
	public static final int ARRAY_ACCESS=8;
	public static final int ARRAY_UPDATE=9;
	public static final int ASSERT=10;
	public static final int ASSIGN=11;
	public static final int ASSUME=12;
	public static final int BLOCK=13;
	public static final int BLOCK_BEGIN=14;
	public static final int BLOCK_END=15;
	public static final int CALL=16;
	public static final int DECREASES=17;
	public static final int DOT=18;
	public static final int DOUBLECOLON=19;
	public static final int ELSE=20;
	public static final int ENSURES=21;
	public static final int EQ=22;
	public static final int EX=23;
	public static final int FUNCTION=24;
	public static final int GE=25;
	public static final int GT=26;
	public static final int HAVOC=27;
	public static final int ID=28;
	public static final int IF=29;
	public static final int IMPLIES=30;
	public static final int INT=31;
	public static final int INTERSECT=32;
	public static final int INVARIANT=33;
	public static final int LABEL=34;
	public static final int LE=35;
	public static final int LEMMA=36;
	public static final int LENGTH=37;
	public static final int LISTEX=38;
	public static final int LIT=39;
	public static final int LT=40;
	public static final int METHOD=41;
	public static final int MINUS=42;
	public static final int MULTILINE_COMMENT=43;
	public static final int NOT=44;
	public static final int OR=45;
	public static final int PLUS=46;
	public static final int REQUIRES=47;
	public static final int RESULTS=48;
	public static final int RETURNS=49;
	public static final int SET=50;
	public static final int SETEX=51;
	public static final int SINGLELINE_COMMENT=52;
	public static final int THEN=53;
	public static final int TIMES=54;
	public static final int UNION=55;
	public static final int VAR=56;
	public static final int WHILE=57;
	public static final int WS=58;

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

	// $ANTLR start "T__59"
	public final void mT__59() throws RecognitionException {
		try {
			int _type = T__59;
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
	// $ANTLR end "T__59"

	// $ANTLR start "T__60"
	public final void mT__60() throws RecognitionException {
		try {
			int _type = T__60;
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
	// $ANTLR end "T__60"

	// $ANTLR start "T__61"
	public final void mT__61() throws RecognitionException {
		try {
			int _type = T__61;
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
	// $ANTLR end "T__61"

	// $ANTLR start "T__62"
	public final void mT__62() throws RecognitionException {
		try {
			int _type = T__62;
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
	// $ANTLR end "T__62"

	// $ANTLR start "T__63"
	public final void mT__63() throws RecognitionException {
		try {
			int _type = T__63;
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
	// $ANTLR end "T__63"

	// $ANTLR start "T__64"
	public final void mT__64() throws RecognitionException {
		try {
			int _type = T__64;
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
	// $ANTLR end "T__64"

	// $ANTLR start "T__65"
	public final void mT__65() throws RecognitionException {
		try {
			int _type = T__65;
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
	// $ANTLR end "T__65"

	// $ANTLR start "INT"
	public final void mINT() throws RecognitionException {
		try {
			int _type = INT;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// Dafny.g:58:5: ( 'int' )
			// Dafny.g:58:7: 'int'
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
			// Dafny.g:59:5: ( 'set' )
			// Dafny.g:59:7: 'set'
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
			// Dafny.g:60:9: ( 'returns' )
			// Dafny.g:60:11: 'returns'
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
			// Dafny.g:61:8: ( 'ensures' )
			// Dafny.g:61:10: 'ensures'
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
			// Dafny.g:62:9: ( 'requires' )
			// Dafny.g:62:11: 'requires'
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
			// Dafny.g:63:10: ( 'decreases' )
			// Dafny.g:63:12: 'decreases'
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

	// $ANTLR start "FUNCTION"
	public final void mFUNCTION() throws RecognitionException {
		try {
			int _type = FUNCTION;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// Dafny.g:64:9: ( 'function' )
			// Dafny.g:64:11: 'function'
			{
			match("function"); 

			}

			state.type = _type;
			state.channel = _channel;
		}
		finally {
			// do for sure before leaving
		}
	}
	// $ANTLR end "FUNCTION"

	// $ANTLR start "METHOD"
	public final void mMETHOD() throws RecognitionException {
		try {
			int _type = METHOD;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// Dafny.g:65:7: ( 'method' )
			// Dafny.g:65:9: 'method'
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
			// Dafny.g:66:6: ( 'lemma' )
			// Dafny.g:66:8: 'lemma'
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
			// Dafny.g:67:6: ( 'label' )
			// Dafny.g:67:8: 'label'
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
			// Dafny.g:68:5: ( 'else' )
			// Dafny.g:68:7: 'else'
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
			// Dafny.g:69:3: ( 'if' )
			// Dafny.g:69:5: 'if'
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
			// Dafny.g:70:5: ( 'then' )
			// Dafny.g:70:7: 'then'
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
			// Dafny.g:71:6: ( 'while' )
			// Dafny.g:71:8: 'while'
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
			// Dafny.g:72:4: ( 'var' )
			// Dafny.g:72:6: 'var'
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
			// Dafny.g:73:5: ( 'call' )
			// Dafny.g:73:6: 'call'
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
			// Dafny.g:74:10: ( 'invariant' )
			// Dafny.g:74:12: 'invariant'
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
			// Dafny.g:75:7: ( 'assert' )
			// Dafny.g:75:9: 'assert'
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

	// $ANTLR start "ASSUME"
	public final void mASSUME() throws RecognitionException {
		try {
			int _type = ASSUME;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// Dafny.g:76:7: ( 'assume' )
			// Dafny.g:76:9: 'assume'
			{
			match("assume"); 

			}

			state.type = _type;
			state.channel = _channel;
		}
		finally {
			// do for sure before leaving
		}
	}
	// $ANTLR end "ASSUME"

	// $ANTLR start "ALL"
	public final void mALL() throws RecognitionException {
		try {
			int _type = ALL;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// Dafny.g:78:4: ( 'forall' )
			// Dafny.g:78:6: 'forall'
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
			// Dafny.g:79:3: ( 'exists' )
			// Dafny.g:79:5: 'exists'
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
			// Dafny.g:81:12: ( '::' )
			// Dafny.g:81:14: '::'
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
			// Dafny.g:82:7: ( ':=' )
			// Dafny.g:82:9: ':='
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
			// Dafny.g:83:3: ( '||' )
			// Dafny.g:83:5: '||'
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
			// Dafny.g:84:4: ( '&&' )
			// Dafny.g:84:6: '&&'
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
			// Dafny.g:85:8: ( '==>' )
			// Dafny.g:85:10: '==>'
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
			// Dafny.g:86:5: ( '+' )
			// Dafny.g:86:7: '+'
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
			// Dafny.g:87:6: ( '-' )
			// Dafny.g:87:8: '-'
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
			// Dafny.g:88:4: ( '!' )
			// Dafny.g:88:6: '!'
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
			// Dafny.g:89:6: ( '*' )
			// Dafny.g:89:8: '*'
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
			// Dafny.g:90:6: ( '++' )
			// Dafny.g:90:8: '++'
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
			// Dafny.g:91:10: ( '**' )
			// Dafny.g:91:12: '**'
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
			// Dafny.g:92:3: ( '<' )
			// Dafny.g:92:5: '<'
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
			// Dafny.g:93:3: ( '<=' )
			// Dafny.g:93:5: '<='
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
			// Dafny.g:94:3: ( '>' )
			// Dafny.g:94:5: '>'
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
			// Dafny.g:95:3: ( '>=' )
			// Dafny.g:95:5: '>='
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
			// Dafny.g:96:3: ( '==' )
			// Dafny.g:96:5: '=='
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
			// Dafny.g:97:4: ( '.' )
			// Dafny.g:97:6: '.'
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
			// Dafny.g:98:12: ( '{' )
			// Dafny.g:98:14: '{'
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
			// Dafny.g:99:10: ( '}' )
			// Dafny.g:99:12: '}'
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
			// Dafny.g:101:7: ( 'Length' ( '0' .. '9' )* )
			// Dafny.g:101:9: 'Length' ( '0' .. '9' )*
			{
			match("Length"); 

			// Dafny.g:101:18: ( '0' .. '9' )*
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
			// Dafny.g:102:7: ( 'array' ( ( '1' .. '9' ) ( '0' .. '9' )* )? )
			// Dafny.g:102:9: 'array' ( ( '1' .. '9' ) ( '0' .. '9' )* )?
			{
			match("array"); 

			// Dafny.g:102:17: ( ( '1' .. '9' ) ( '0' .. '9' )* )?
			int alt3=2;
			int LA3_0 = input.LA(1);
			if ( ((LA3_0 >= '1' && LA3_0 <= '9')) ) {
				alt3=1;
			}
			switch (alt3) {
				case 1 :
					// Dafny.g:102:18: ( '1' .. '9' ) ( '0' .. '9' )*
					{
					if ( (input.LA(1) >= '1' && input.LA(1) <= '9') ) {
						input.consume();
					}
					else {
						MismatchedSetException mse = new MismatchedSetException(null,input);
						recover(mse);
						throw mse;
					}
					// Dafny.g:102:31: ( '0' .. '9' )*
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
			// Dafny.g:103:4: ( ( 'a' .. 'z' | 'A' .. 'Z' | '_' ) ( 'a' .. 'z' | 'A' .. 'Z' | '0' .. '9' | '_' )* )
			// Dafny.g:103:6: ( 'a' .. 'z' | 'A' .. 'Z' | '_' ) ( 'a' .. 'z' | 'A' .. 'Z' | '0' .. '9' | '_' )*
			{
			if ( (input.LA(1) >= 'A' && input.LA(1) <= 'Z')||input.LA(1)=='_'||(input.LA(1) >= 'a' && input.LA(1) <= 'z') ) {
				input.consume();
			}
			else {
				MismatchedSetException mse = new MismatchedSetException(null,input);
				recover(mse);
				throw mse;
			}
			// Dafny.g:103:38: ( 'a' .. 'z' | 'A' .. 'Z' | '0' .. '9' | '_' )*
			loop4:
			while (true) {
				int alt4=2;
				int LA4_0 = input.LA(1);
				if ( ((LA4_0 >= '0' && LA4_0 <= '9')||(LA4_0 >= 'A' && LA4_0 <= 'Z')||LA4_0=='_'||(LA4_0 >= 'a' && LA4_0 <= 'z')) ) {
					alt4=1;
				}

				switch (alt4) {
				case 1 :
					// Dafny.g:
					{
					if ( (input.LA(1) >= '0' && input.LA(1) <= '9')||(input.LA(1) >= 'A' && input.LA(1) <= 'Z')||input.LA(1)=='_'||(input.LA(1) >= 'a' && input.LA(1) <= 'z') ) {
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
					break loop4;
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
	// $ANTLR end "ID"

	// $ANTLR start "LIT"
	public final void mLIT() throws RecognitionException {
		try {
			int _type = LIT;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// Dafny.g:104:5: ( ( '0' .. '9' )+ )
			// Dafny.g:104:7: ( '0' .. '9' )+
			{
			// Dafny.g:104:7: ( '0' .. '9' )+
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
			// Dafny.g:106:4: ( ( ' ' | '\\n' | '\\r' ) )
			// Dafny.g:106:6: ( ' ' | '\\n' | '\\r' )
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

	// $ANTLR start "SINGLELINE_COMMENT"
	public final void mSINGLELINE_COMMENT() throws RecognitionException {
		try {
			int _type = SINGLELINE_COMMENT;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// Dafny.g:107:19: ( '//' (~ ( '\\r' | '\\n' ) )* )
			// Dafny.g:107:21: '//' (~ ( '\\r' | '\\n' ) )*
			{
			match("//"); 

			// Dafny.g:107:26: (~ ( '\\r' | '\\n' ) )*
			loop6:
			while (true) {
				int alt6=2;
				int LA6_0 = input.LA(1);
				if ( ((LA6_0 >= '\u0000' && LA6_0 <= '\t')||(LA6_0 >= '\u000B' && LA6_0 <= '\f')||(LA6_0 >= '\u000E' && LA6_0 <= '\uFFFF')) ) {
					alt6=1;
				}

				switch (alt6) {
				case 1 :
					// Dafny.g:
					{
					if ( (input.LA(1) >= '\u0000' && input.LA(1) <= '\t')||(input.LA(1) >= '\u000B' && input.LA(1) <= '\f')||(input.LA(1) >= '\u000E' && input.LA(1) <= '\uFFFF') ) {
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
					break loop6;
				}
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
	// $ANTLR end "SINGLELINE_COMMENT"

	// $ANTLR start "MULTILINE_COMMENT"
	public final void mMULTILINE_COMMENT() throws RecognitionException {
		try {
			int _type = MULTILINE_COMMENT;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// Dafny.g:108:18: ( '/*' ( . )* '*/' )
			// Dafny.g:108:20: '/*' ( . )* '*/'
			{
			match("/*"); 

			// Dafny.g:108:25: ( . )*
			loop7:
			while (true) {
				int alt7=2;
				int LA7_0 = input.LA(1);
				if ( (LA7_0=='*') ) {
					int LA7_1 = input.LA(2);
					if ( (LA7_1=='/') ) {
						alt7=2;
					}
					else if ( ((LA7_1 >= '\u0000' && LA7_1 <= '.')||(LA7_1 >= '0' && LA7_1 <= '\uFFFF')) ) {
						alt7=1;
					}

				}
				else if ( ((LA7_0 >= '\u0000' && LA7_0 <= ')')||(LA7_0 >= '+' && LA7_0 <= '\uFFFF')) ) {
					alt7=1;
				}

				switch (alt7) {
				case 1 :
					// Dafny.g:108:25: .
					{
					matchAny(); 
					}
					break;

				default :
					break loop7;
				}
			}

			match("*/"); 

			 _channel = HIDDEN; 
			}

			state.type = _type;
			state.channel = _channel;
		}
		finally {
			// do for sure before leaving
		}
	}
	// $ANTLR end "MULTILINE_COMMENT"

	@Override
	public void mTokens() throws RecognitionException {
		// Dafny.g:1:8: ( T__59 | T__60 | T__61 | T__62 | T__63 | T__64 | T__65 | INT | SET | RETURNS | ENSURES | REQUIRES | DECREASES | FUNCTION | METHOD | LEMMA | LABEL | ELSE | IF | THEN | WHILE | VAR | CALL | INVARIANT | ASSERT | ASSUME | ALL | EX | DOUBLECOLON | ASSIGN | OR | AND | IMPLIES | PLUS | MINUS | NOT | TIMES | UNION | INTERSECT | LT | LE | GT | GE | EQ | DOT | BLOCK_BEGIN | BLOCK_END | LENGTH | ARRAY | ID | LIT | WS | SINGLELINE_COMMENT | MULTILINE_COMMENT )
		int alt8=54;
		alt8 = dfa8.predict(input);
		switch (alt8) {
			case 1 :
				// Dafny.g:1:10: T__59
				{
				mT__59(); 

				}
				break;
			case 2 :
				// Dafny.g:1:16: T__60
				{
				mT__60(); 

				}
				break;
			case 3 :
				// Dafny.g:1:22: T__61
				{
				mT__61(); 

				}
				break;
			case 4 :
				// Dafny.g:1:28: T__62
				{
				mT__62(); 

				}
				break;
			case 5 :
				// Dafny.g:1:34: T__63
				{
				mT__63(); 

				}
				break;
			case 6 :
				// Dafny.g:1:40: T__64
				{
				mT__64(); 

				}
				break;
			case 7 :
				// Dafny.g:1:46: T__65
				{
				mT__65(); 

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
				// Dafny.g:1:95: FUNCTION
				{
				mFUNCTION(); 

				}
				break;
			case 15 :
				// Dafny.g:1:104: METHOD
				{
				mMETHOD(); 

				}
				break;
			case 16 :
				// Dafny.g:1:111: LEMMA
				{
				mLEMMA(); 

				}
				break;
			case 17 :
				// Dafny.g:1:117: LABEL
				{
				mLABEL(); 

				}
				break;
			case 18 :
				// Dafny.g:1:123: ELSE
				{
				mELSE(); 

				}
				break;
			case 19 :
				// Dafny.g:1:128: IF
				{
				mIF(); 

				}
				break;
			case 20 :
				// Dafny.g:1:131: THEN
				{
				mTHEN(); 

				}
				break;
			case 21 :
				// Dafny.g:1:136: WHILE
				{
				mWHILE(); 

				}
				break;
			case 22 :
				// Dafny.g:1:142: VAR
				{
				mVAR(); 

				}
				break;
			case 23 :
				// Dafny.g:1:146: CALL
				{
				mCALL(); 

				}
				break;
			case 24 :
				// Dafny.g:1:151: INVARIANT
				{
				mINVARIANT(); 

				}
				break;
			case 25 :
				// Dafny.g:1:161: ASSERT
				{
				mASSERT(); 

				}
				break;
			case 26 :
				// Dafny.g:1:168: ASSUME
				{
				mASSUME(); 

				}
				break;
			case 27 :
				// Dafny.g:1:175: ALL
				{
				mALL(); 

				}
				break;
			case 28 :
				// Dafny.g:1:179: EX
				{
				mEX(); 

				}
				break;
			case 29 :
				// Dafny.g:1:182: DOUBLECOLON
				{
				mDOUBLECOLON(); 

				}
				break;
			case 30 :
				// Dafny.g:1:194: ASSIGN
				{
				mASSIGN(); 

				}
				break;
			case 31 :
				// Dafny.g:1:201: OR
				{
				mOR(); 

				}
				break;
			case 32 :
				// Dafny.g:1:204: AND
				{
				mAND(); 

				}
				break;
			case 33 :
				// Dafny.g:1:208: IMPLIES
				{
				mIMPLIES(); 

				}
				break;
			case 34 :
				// Dafny.g:1:216: PLUS
				{
				mPLUS(); 

				}
				break;
			case 35 :
				// Dafny.g:1:221: MINUS
				{
				mMINUS(); 

				}
				break;
			case 36 :
				// Dafny.g:1:227: NOT
				{
				mNOT(); 

				}
				break;
			case 37 :
				// Dafny.g:1:231: TIMES
				{
				mTIMES(); 

				}
				break;
			case 38 :
				// Dafny.g:1:237: UNION
				{
				mUNION(); 

				}
				break;
			case 39 :
				// Dafny.g:1:243: INTERSECT
				{
				mINTERSECT(); 

				}
				break;
			case 40 :
				// Dafny.g:1:253: LT
				{
				mLT(); 

				}
				break;
			case 41 :
				// Dafny.g:1:256: LE
				{
				mLE(); 

				}
				break;
			case 42 :
				// Dafny.g:1:259: GT
				{
				mGT(); 

				}
				break;
			case 43 :
				// Dafny.g:1:262: GE
				{
				mGE(); 

				}
				break;
			case 44 :
				// Dafny.g:1:265: EQ
				{
				mEQ(); 

				}
				break;
			case 45 :
				// Dafny.g:1:268: DOT
				{
				mDOT(); 

				}
				break;
			case 46 :
				// Dafny.g:1:272: BLOCK_BEGIN
				{
				mBLOCK_BEGIN(); 

				}
				break;
			case 47 :
				// Dafny.g:1:284: BLOCK_END
				{
				mBLOCK_END(); 

				}
				break;
			case 48 :
				// Dafny.g:1:294: LENGTH
				{
				mLENGTH(); 

				}
				break;
			case 49 :
				// Dafny.g:1:301: ARRAY
				{
				mARRAY(); 

				}
				break;
			case 50 :
				// Dafny.g:1:307: ID
				{
				mID(); 

				}
				break;
			case 51 :
				// Dafny.g:1:310: LIT
				{
				mLIT(); 

				}
				break;
			case 52 :
				// Dafny.g:1:314: WS
				{
				mWS(); 

				}
				break;
			case 53 :
				// Dafny.g:1:317: SINGLELINE_COMMENT
				{
				mSINGLELINE_COMMENT(); 

				}
				break;
			case 54 :
				// Dafny.g:1:336: MULTILINE_COMMENT
				{
				mMULTILINE_COMMENT(); 

				}
				break;

		}
	}


	protected DFA8 dfa8 = new DFA8(this);
	static final String DFA8_eotS =
		"\4\uffff\1\50\3\uffff\15\42\3\uffff\1\76\2\uffff\1\100\1\102\1\104\3\uffff"+
		"\1\42\7\uffff\1\42\1\112\21\42\1\136\10\uffff\1\42\2\uffff\1\140\1\42"+
		"\1\uffff\1\142\15\42\1\160\3\42\2\uffff\1\42\1\uffff\1\42\1\uffff\3\42"+
		"\1\172\7\42\1\u0082\1\42\1\uffff\1\u0084\10\42\1\uffff\5\42\1\u0092\1"+
		"\u0093\1\uffff\1\u0094\1\uffff\2\42\1\u0098\5\42\1\u009e\2\42\1\u00a1"+
		"\1\u00a2\3\uffff\1\u00a3\1\u00a4\1\u0098\1\uffff\1\u00a7\1\42\1\u00a9"+
		"\1\42\1\u00ab\1\uffff\2\42\4\uffff\1\u0098\1\u00a7\1\uffff\1\42\1\uffff"+
		"\1\u00af\1\uffff\1\42\1\u00b1\1\u00b2\1\uffff\1\u00b3\3\uffff";
	static final String DFA8_eofS =
		"\u00b4\uffff";
	static final String DFA8_minS =
		"\1\12\3\uffff\1\72\3\uffff\1\146\2\145\1\154\1\145\1\157\1\145\1\141\2"+
		"\150\2\141\1\162\2\uffff\1\75\1\53\2\uffff\1\52\2\75\3\uffff\1\145\3\uffff"+
		"\1\52\3\uffff\1\164\1\60\1\164\1\161\2\163\1\151\1\143\1\156\1\162\1\164"+
		"\1\155\1\142\1\145\1\151\1\162\1\154\1\163\1\162\1\76\10\uffff\1\156\2"+
		"\uffff\1\60\1\141\1\uffff\1\60\3\165\1\145\1\163\1\162\1\143\1\141\1\150"+
		"\1\155\1\145\1\156\1\154\1\60\1\154\1\145\1\141\2\uffff\1\147\1\uffff"+
		"\1\162\1\uffff\1\162\1\151\1\162\1\60\1\164\1\145\1\164\1\154\1\157\1"+
		"\141\1\154\1\60\1\145\1\uffff\1\60\1\162\1\155\1\171\1\164\1\151\1\156"+
		"\1\162\1\145\1\uffff\1\163\1\141\1\151\1\154\1\144\2\60\1\uffff\1\60\1"+
		"\uffff\1\164\1\145\1\60\1\150\1\141\1\163\1\145\1\163\1\60\1\163\1\157"+
		"\2\60\3\uffff\3\60\1\uffff\1\60\1\156\1\60\1\163\1\60\1\uffff\1\145\1"+
		"\156\4\uffff\2\60\1\uffff\1\164\1\uffff\1\60\1\uffff\1\163\2\60\1\uffff"+
		"\1\60\3\uffff";
	static final String DFA8_maxS =
		"\1\175\3\uffff\1\75\3\uffff\1\156\2\145\1\170\1\145\1\165\2\145\2\150"+
		"\2\141\1\163\2\uffff\1\75\1\53\2\uffff\1\52\2\75\3\uffff\1\145\3\uffff"+
		"\1\57\3\uffff\1\166\1\172\2\164\2\163\1\151\1\143\1\156\1\162\1\164\1"+
		"\155\1\142\1\145\1\151\1\162\1\154\1\163\1\162\1\76\10\uffff\1\156\2\uffff"+
		"\1\172\1\141\1\uffff\1\172\3\165\1\145\1\163\1\162\1\143\1\141\1\150\1"+
		"\155\1\145\1\156\1\154\1\172\1\154\1\165\1\141\2\uffff\1\147\1\uffff\1"+
		"\162\1\uffff\1\162\1\151\1\162\1\172\1\164\1\145\1\164\1\154\1\157\1\141"+
		"\1\154\1\172\1\145\1\uffff\1\172\1\162\1\155\1\171\1\164\1\151\1\156\1"+
		"\162\1\145\1\uffff\1\163\1\141\1\151\1\154\1\144\2\172\1\uffff\1\172\1"+
		"\uffff\1\164\1\145\1\172\1\150\1\141\1\163\1\145\1\163\1\172\1\163\1\157"+
		"\2\172\3\uffff\3\172\1\uffff\1\172\1\156\1\172\1\163\1\172\1\uffff\1\145"+
		"\1\156\4\uffff\2\172\1\uffff\1\164\1\uffff\1\172\1\uffff\1\163\2\172\1"+
		"\uffff\1\172\3\uffff";
	static final String DFA8_acceptS =
		"\1\uffff\1\1\1\2\1\3\1\uffff\1\5\1\6\1\7\15\uffff\1\37\1\40\2\uffff\1"+
		"\43\1\44\3\uffff\1\55\1\56\1\57\1\uffff\1\62\1\63\1\64\1\uffff\1\35\1"+
		"\36\1\4\24\uffff\1\46\1\42\1\47\1\45\1\51\1\50\1\53\1\52\1\uffff\1\65"+
		"\1\66\2\uffff\1\23\22\uffff\1\41\1\54\1\uffff\1\10\1\uffff\1\11\15\uffff"+
		"\1\26\11\uffff\1\22\7\uffff\1\24\1\uffff\1\27\15\uffff\1\20\1\21\1\25"+
		"\3\uffff\1\61\5\uffff\1\34\2\uffff\1\33\1\17\1\31\1\32\2\uffff\1\60\1"+
		"\uffff\1\12\1\uffff\1\13\3\uffff\1\14\1\uffff\1\16\1\30\1\15";
	static final String DFA8_specialS =
		"\u00b4\uffff}>";
	static final String[] DFA8_transitionS = {
			"\1\44\2\uffff\1\44\22\uffff\1\44\1\32\4\uffff\1\26\1\uffff\1\1\1\2\1"+
			"\33\1\30\1\3\1\31\1\36\1\45\12\43\1\4\1\5\1\34\1\27\1\35\2\uffff\13\42"+
			"\1\41\16\42\1\6\1\uffff\1\7\1\uffff\1\42\1\uffff\1\24\1\42\1\23\1\14"+
			"\1\13\1\15\2\42\1\10\2\42\1\17\1\16\4\42\1\12\1\11\1\20\1\42\1\22\1\21"+
			"\3\42\1\37\1\25\1\40",
			"",
			"",
			"",
			"\1\46\2\uffff\1\47",
			"",
			"",
			"",
			"\1\52\7\uffff\1\51",
			"\1\53",
			"\1\54",
			"\1\56\1\uffff\1\55\11\uffff\1\57",
			"\1\60",
			"\1\62\5\uffff\1\61",
			"\1\63",
			"\1\65\3\uffff\1\64",
			"\1\66",
			"\1\67",
			"\1\70",
			"\1\71",
			"\1\73\1\72",
			"",
			"",
			"\1\74",
			"\1\75",
			"",
			"",
			"\1\77",
			"\1\101",
			"\1\103",
			"",
			"",
			"",
			"\1\105",
			"",
			"",
			"",
			"\1\107\4\uffff\1\106",
			"",
			"",
			"",
			"\1\110\1\uffff\1\111",
			"\12\42\7\uffff\32\42\4\uffff\1\42\1\uffff\32\42",
			"\1\113",
			"\1\115\2\uffff\1\114",
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
			"\1\131",
			"\1\132",
			"\1\133",
			"\1\134",
			"\1\135",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"\1\137",
			"",
			"",
			"\12\42\7\uffff\32\42\4\uffff\1\42\1\uffff\32\42",
			"\1\141",
			"",
			"\12\42\7\uffff\32\42\4\uffff\1\42\1\uffff\32\42",
			"\1\143",
			"\1\144",
			"\1\145",
			"\1\146",
			"\1\147",
			"\1\150",
			"\1\151",
			"\1\152",
			"\1\153",
			"\1\154",
			"\1\155",
			"\1\156",
			"\1\157",
			"\12\42\7\uffff\32\42\4\uffff\1\42\1\uffff\32\42",
			"\1\161",
			"\1\162\17\uffff\1\163",
			"\1\164",
			"",
			"",
			"\1\165",
			"",
			"\1\166",
			"",
			"\1\167",
			"\1\170",
			"\1\171",
			"\12\42\7\uffff\32\42\4\uffff\1\42\1\uffff\32\42",
			"\1\173",
			"\1\174",
			"\1\175",
			"\1\176",
			"\1\177",
			"\1\u0080",
			"\1\u0081",
			"\12\42\7\uffff\32\42\4\uffff\1\42\1\uffff\32\42",
			"\1\u0083",
			"",
			"\12\42\7\uffff\32\42\4\uffff\1\42\1\uffff\32\42",
			"\1\u0085",
			"\1\u0086",
			"\1\u0087",
			"\1\u0088",
			"\1\u0089",
			"\1\u008a",
			"\1\u008b",
			"\1\u008c",
			"",
			"\1\u008d",
			"\1\u008e",
			"\1\u008f",
			"\1\u0090",
			"\1\u0091",
			"\12\42\7\uffff\32\42\4\uffff\1\42\1\uffff\32\42",
			"\12\42\7\uffff\32\42\4\uffff\1\42\1\uffff\32\42",
			"",
			"\12\42\7\uffff\32\42\4\uffff\1\42\1\uffff\32\42",
			"",
			"\1\u0095",
			"\1\u0096",
			"\1\42\11\u0097\7\uffff\32\42\4\uffff\1\42\1\uffff\32\42",
			"\1\u0099",
			"\1\u009a",
			"\1\u009b",
			"\1\u009c",
			"\1\u009d",
			"\12\42\7\uffff\32\42\4\uffff\1\42\1\uffff\32\42",
			"\1\u009f",
			"\1\u00a0",
			"\12\42\7\uffff\32\42\4\uffff\1\42\1\uffff\32\42",
			"\12\42\7\uffff\32\42\4\uffff\1\42\1\uffff\32\42",
			"",
			"",
			"",
			"\12\42\7\uffff\32\42\4\uffff\1\42\1\uffff\32\42",
			"\12\42\7\uffff\32\42\4\uffff\1\42\1\uffff\32\42",
			"\12\u00a5\7\uffff\32\42\4\uffff\1\42\1\uffff\32\42",
			"",
			"\12\u00a6\7\uffff\32\42\4\uffff\1\42\1\uffff\32\42",
			"\1\u00a8",
			"\12\42\7\uffff\32\42\4\uffff\1\42\1\uffff\32\42",
			"\1\u00aa",
			"\12\42\7\uffff\32\42\4\uffff\1\42\1\uffff\32\42",
			"",
			"\1\u00ac",
			"\1\u00ad",
			"",
			"",
			"",
			"",
			"\12\u00a5\7\uffff\32\42\4\uffff\1\42\1\uffff\32\42",
			"\12\u00a6\7\uffff\32\42\4\uffff\1\42\1\uffff\32\42",
			"",
			"\1\u00ae",
			"",
			"\12\42\7\uffff\32\42\4\uffff\1\42\1\uffff\32\42",
			"",
			"\1\u00b0",
			"\12\42\7\uffff\32\42\4\uffff\1\42\1\uffff\32\42",
			"\12\42\7\uffff\32\42\4\uffff\1\42\1\uffff\32\42",
			"",
			"\12\42\7\uffff\32\42\4\uffff\1\42\1\uffff\32\42",
			"",
			"",
			""
	};

	static final short[] DFA8_eot = DFA.unpackEncodedString(DFA8_eotS);
	static final short[] DFA8_eof = DFA.unpackEncodedString(DFA8_eofS);
	static final char[] DFA8_min = DFA.unpackEncodedStringToUnsignedChars(DFA8_minS);
	static final char[] DFA8_max = DFA.unpackEncodedStringToUnsignedChars(DFA8_maxS);
	static final short[] DFA8_accept = DFA.unpackEncodedString(DFA8_acceptS);
	static final short[] DFA8_special = DFA.unpackEncodedString(DFA8_specialS);
	static final short[][] DFA8_transition;

	static {
		int numStates = DFA8_transitionS.length;
		DFA8_transition = new short[numStates][];
		for (int i=0; i<numStates; i++) {
			DFA8_transition[i] = DFA.unpackEncodedString(DFA8_transitionS[i]);
		}
	}

	protected class DFA8 extends DFA {

		public DFA8(BaseRecognizer recognizer) {
			this.recognizer = recognizer;
			this.decisionNumber = 8;
			this.eot = DFA8_eot;
			this.eof = DFA8_eof;
			this.min = DFA8_min;
			this.max = DFA8_max;
			this.accept = DFA8_accept;
			this.special = DFA8_special;
			this.transition = DFA8_transition;
		}
		@Override
		public String getDescription() {
			return "1:1: Tokens : ( T__59 | T__60 | T__61 | T__62 | T__63 | T__64 | T__65 | INT | SET | RETURNS | ENSURES | REQUIRES | DECREASES | FUNCTION | METHOD | LEMMA | LABEL | ELSE | IF | THEN | WHILE | VAR | CALL | INVARIANT | ASSERT | ASSUME | ALL | EX | DOUBLECOLON | ASSIGN | OR | AND | IMPLIES | PLUS | MINUS | NOT | TIMES | UNION | INTERSECT | LT | LE | GT | GE | EQ | DOT | BLOCK_BEGIN | BLOCK_END | LENGTH | ARRAY | ID | LIT | WS | SINGLELINE_COMMENT | MULTILINE_COMMENT );";
		}
	}

}
