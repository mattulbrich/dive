// $ANTLR 3.5.1 src/edu/kit/iti/algover/parser/Dafny.g 2016-06-17 19:22:10

  package edu.kit.iti.algover.parser;


import org.antlr.runtime.*;
import java.util.Stack;
import java.util.List;
import java.util.ArrayList;

@SuppressWarnings("all")
public class DafnyLexer extends Lexer {
	public static final int EOF=-1;
	public static final int T__68=68;
	public static final int T__69=69;
	public static final int T__70=70;
	public static final int T__71=71;
	public static final int T__72=72;
	public static final int T__73=73;
	public static final int T__74=74;
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
	public static final int BOOL=16;
	public static final int CALL=17;
	public static final int CLASS=18;
	public static final int DECREASES=19;
	public static final int DOT=20;
	public static final int DOUBLECOLON=21;
	public static final int ELSE=22;
	public static final int ENSURES=23;
	public static final int EQ=24;
	public static final int EX=25;
	public static final int FIELD_ACCESS=26;
	public static final int FUNCTION=27;
	public static final int FUNC_CALL=28;
	public static final int GE=29;
	public static final int GT=30;
	public static final int HAVOC=31;
	public static final int ID=32;
	public static final int IF=33;
	public static final int IMPLIES=34;
	public static final int INT=35;
	public static final int INTERSECT=36;
	public static final int INVARIANT=37;
	public static final int LABEL=38;
	public static final int LE=39;
	public static final int LEMMA=40;
	public static final int LENGTH=41;
	public static final int LISTEX=42;
	public static final int LIT=43;
	public static final int LT=44;
	public static final int METHOD=45;
	public static final int MINUS=46;
	public static final int MODIFIES=47;
	public static final int MULTILINE_COMMENT=48;
	public static final int NEQ=49;
	public static final int NOT=50;
	public static final int NULL=51;
	public static final int OBJ_FUNC_CALL=52;
	public static final int OR=53;
	public static final int PLUS=54;
	public static final int REQUIRES=55;
	public static final int RESULTS=56;
	public static final int RETURNS=57;
	public static final int SET=58;
	public static final int SETEX=59;
	public static final int SINGLELINE_COMMENT=60;
	public static final int THEN=61;
	public static final int THIS=62;
	public static final int TIMES=63;
	public static final int UNION=64;
	public static final int VAR=65;
	public static final int WHILE=66;
	public static final int WS=67;

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
	@Override public String getGrammarFileName() { return "src/edu/kit/iti/algover/parser/Dafny.g"; }

	// $ANTLR start "T__68"
	public final void mT__68() throws RecognitionException {
		try {
			int _type = T__68;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// src/edu/kit/iti/algover/parser/Dafny.g:6:7: ( '(' )
			// src/edu/kit/iti/algover/parser/Dafny.g:6:9: '('
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
	// $ANTLR end "T__68"

	// $ANTLR start "T__69"
	public final void mT__69() throws RecognitionException {
		try {
			int _type = T__69;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// src/edu/kit/iti/algover/parser/Dafny.g:7:7: ( ')' )
			// src/edu/kit/iti/algover/parser/Dafny.g:7:9: ')'
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
	// $ANTLR end "T__69"

	// $ANTLR start "T__70"
	public final void mT__70() throws RecognitionException {
		try {
			int _type = T__70;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// src/edu/kit/iti/algover/parser/Dafny.g:8:7: ( ',' )
			// src/edu/kit/iti/algover/parser/Dafny.g:8:9: ','
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
	// $ANTLR end "T__70"

	// $ANTLR start "T__71"
	public final void mT__71() throws RecognitionException {
		try {
			int _type = T__71;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// src/edu/kit/iti/algover/parser/Dafny.g:9:7: ( ':' )
			// src/edu/kit/iti/algover/parser/Dafny.g:9:9: ':'
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
	// $ANTLR end "T__71"

	// $ANTLR start "T__72"
	public final void mT__72() throws RecognitionException {
		try {
			int _type = T__72;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// src/edu/kit/iti/algover/parser/Dafny.g:10:7: ( ';' )
			// src/edu/kit/iti/algover/parser/Dafny.g:10:9: ';'
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
	// $ANTLR end "T__72"

	// $ANTLR start "T__73"
	public final void mT__73() throws RecognitionException {
		try {
			int _type = T__73;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// src/edu/kit/iti/algover/parser/Dafny.g:11:7: ( '[' )
			// src/edu/kit/iti/algover/parser/Dafny.g:11:9: '['
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
	// $ANTLR end "T__73"

	// $ANTLR start "T__74"
	public final void mT__74() throws RecognitionException {
		try {
			int _type = T__74;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// src/edu/kit/iti/algover/parser/Dafny.g:12:7: ( ']' )
			// src/edu/kit/iti/algover/parser/Dafny.g:12:9: ']'
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
	// $ANTLR end "T__74"

	// $ANTLR start "INT"
	public final void mINT() throws RecognitionException {
		try {
			int _type = INT;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// src/edu/kit/iti/algover/parser/Dafny.g:61:5: ( 'int' )
			// src/edu/kit/iti/algover/parser/Dafny.g:61:7: 'int'
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

	// $ANTLR start "BOOL"
	public final void mBOOL() throws RecognitionException {
		try {
			int _type = BOOL;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// src/edu/kit/iti/algover/parser/Dafny.g:62:6: ( 'bool' )
			// src/edu/kit/iti/algover/parser/Dafny.g:62:8: 'bool'
			{
			match("bool"); 

			}

			state.type = _type;
			state.channel = _channel;
		}
		finally {
			// do for sure before leaving
		}
	}
	// $ANTLR end "BOOL"

	// $ANTLR start "SET"
	public final void mSET() throws RecognitionException {
		try {
			int _type = SET;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// src/edu/kit/iti/algover/parser/Dafny.g:63:5: ( 'set' )
			// src/edu/kit/iti/algover/parser/Dafny.g:63:7: 'set'
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
			// src/edu/kit/iti/algover/parser/Dafny.g:64:9: ( 'returns' )
			// src/edu/kit/iti/algover/parser/Dafny.g:64:11: 'returns'
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
			// src/edu/kit/iti/algover/parser/Dafny.g:65:8: ( 'ensures' )
			// src/edu/kit/iti/algover/parser/Dafny.g:65:10: 'ensures'
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
			// src/edu/kit/iti/algover/parser/Dafny.g:66:9: ( 'requires' )
			// src/edu/kit/iti/algover/parser/Dafny.g:66:11: 'requires'
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
			// src/edu/kit/iti/algover/parser/Dafny.g:67:10: ( 'decreases' )
			// src/edu/kit/iti/algover/parser/Dafny.g:67:12: 'decreases'
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
			// src/edu/kit/iti/algover/parser/Dafny.g:68:9: ( 'function' )
			// src/edu/kit/iti/algover/parser/Dafny.g:68:11: 'function'
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
			// src/edu/kit/iti/algover/parser/Dafny.g:69:7: ( 'method' )
			// src/edu/kit/iti/algover/parser/Dafny.g:69:9: 'method'
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
			// src/edu/kit/iti/algover/parser/Dafny.g:70:6: ( 'lemma' )
			// src/edu/kit/iti/algover/parser/Dafny.g:70:8: 'lemma'
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
			// src/edu/kit/iti/algover/parser/Dafny.g:71:6: ( 'label' )
			// src/edu/kit/iti/algover/parser/Dafny.g:71:8: 'label'
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
			// src/edu/kit/iti/algover/parser/Dafny.g:72:5: ( 'else' )
			// src/edu/kit/iti/algover/parser/Dafny.g:72:7: 'else'
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
			// src/edu/kit/iti/algover/parser/Dafny.g:73:3: ( 'if' )
			// src/edu/kit/iti/algover/parser/Dafny.g:73:5: 'if'
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
			// src/edu/kit/iti/algover/parser/Dafny.g:74:5: ( 'then' )
			// src/edu/kit/iti/algover/parser/Dafny.g:74:7: 'then'
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
			// src/edu/kit/iti/algover/parser/Dafny.g:75:6: ( 'while' )
			// src/edu/kit/iti/algover/parser/Dafny.g:75:8: 'while'
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
			// src/edu/kit/iti/algover/parser/Dafny.g:76:4: ( 'var' )
			// src/edu/kit/iti/algover/parser/Dafny.g:76:6: 'var'
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
			// src/edu/kit/iti/algover/parser/Dafny.g:77:5: ( 'call' )
			// src/edu/kit/iti/algover/parser/Dafny.g:77:6: 'call'
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
			// src/edu/kit/iti/algover/parser/Dafny.g:78:10: ( 'invariant' )
			// src/edu/kit/iti/algover/parser/Dafny.g:78:12: 'invariant'
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
			// src/edu/kit/iti/algover/parser/Dafny.g:79:7: ( 'assert' )
			// src/edu/kit/iti/algover/parser/Dafny.g:79:9: 'assert'
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
			// src/edu/kit/iti/algover/parser/Dafny.g:80:7: ( 'assume' )
			// src/edu/kit/iti/algover/parser/Dafny.g:80:9: 'assume'
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

	// $ANTLR start "MODIFIES"
	public final void mMODIFIES() throws RecognitionException {
		try {
			int _type = MODIFIES;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// src/edu/kit/iti/algover/parser/Dafny.g:81:9: ( 'modifies' )
			// src/edu/kit/iti/algover/parser/Dafny.g:81:11: 'modifies'
			{
			match("modifies"); 

			}

			state.type = _type;
			state.channel = _channel;
		}
		finally {
			// do for sure before leaving
		}
	}
	// $ANTLR end "MODIFIES"

	// $ANTLR start "CLASS"
	public final void mCLASS() throws RecognitionException {
		try {
			int _type = CLASS;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// src/edu/kit/iti/algover/parser/Dafny.g:82:6: ( 'class' )
			// src/edu/kit/iti/algover/parser/Dafny.g:82:8: 'class'
			{
			match("class"); 

			}

			state.type = _type;
			state.channel = _channel;
		}
		finally {
			// do for sure before leaving
		}
	}
	// $ANTLR end "CLASS"

	// $ANTLR start "THIS"
	public final void mTHIS() throws RecognitionException {
		try {
			int _type = THIS;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// src/edu/kit/iti/algover/parser/Dafny.g:83:5: ( 'this' )
			// src/edu/kit/iti/algover/parser/Dafny.g:83:7: 'this'
			{
			match("this"); 

			}

			state.type = _type;
			state.channel = _channel;
		}
		finally {
			// do for sure before leaving
		}
	}
	// $ANTLR end "THIS"

	// $ANTLR start "NULL"
	public final void mNULL() throws RecognitionException {
		try {
			int _type = NULL;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// src/edu/kit/iti/algover/parser/Dafny.g:84:5: ( 'null' )
			// src/edu/kit/iti/algover/parser/Dafny.g:84:7: 'null'
			{
			match("null"); 

			}

			state.type = _type;
			state.channel = _channel;
		}
		finally {
			// do for sure before leaving
		}
	}
	// $ANTLR end "NULL"

	// $ANTLR start "ALL"
	public final void mALL() throws RecognitionException {
		try {
			int _type = ALL;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// src/edu/kit/iti/algover/parser/Dafny.g:86:4: ( 'forall' )
			// src/edu/kit/iti/algover/parser/Dafny.g:86:6: 'forall'
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
			// src/edu/kit/iti/algover/parser/Dafny.g:87:3: ( 'exists' )
			// src/edu/kit/iti/algover/parser/Dafny.g:87:5: 'exists'
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
			// src/edu/kit/iti/algover/parser/Dafny.g:89:12: ( '::' )
			// src/edu/kit/iti/algover/parser/Dafny.g:89:14: '::'
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
			// src/edu/kit/iti/algover/parser/Dafny.g:90:7: ( ':=' )
			// src/edu/kit/iti/algover/parser/Dafny.g:90:9: ':='
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
			// src/edu/kit/iti/algover/parser/Dafny.g:91:3: ( '||' )
			// src/edu/kit/iti/algover/parser/Dafny.g:91:5: '||'
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
			// src/edu/kit/iti/algover/parser/Dafny.g:92:4: ( '&&' )
			// src/edu/kit/iti/algover/parser/Dafny.g:92:6: '&&'
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
			// src/edu/kit/iti/algover/parser/Dafny.g:93:8: ( '==>' )
			// src/edu/kit/iti/algover/parser/Dafny.g:93:10: '==>'
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
			// src/edu/kit/iti/algover/parser/Dafny.g:94:5: ( '+' )
			// src/edu/kit/iti/algover/parser/Dafny.g:94:7: '+'
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
			// src/edu/kit/iti/algover/parser/Dafny.g:95:6: ( '-' )
			// src/edu/kit/iti/algover/parser/Dafny.g:95:8: '-'
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
			// src/edu/kit/iti/algover/parser/Dafny.g:96:4: ( '!' )
			// src/edu/kit/iti/algover/parser/Dafny.g:96:6: '!'
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
			// src/edu/kit/iti/algover/parser/Dafny.g:97:6: ( '*' )
			// src/edu/kit/iti/algover/parser/Dafny.g:97:8: '*'
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
			// src/edu/kit/iti/algover/parser/Dafny.g:98:6: ( '++' )
			// src/edu/kit/iti/algover/parser/Dafny.g:98:8: '++'
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
			// src/edu/kit/iti/algover/parser/Dafny.g:99:10: ( '**' )
			// src/edu/kit/iti/algover/parser/Dafny.g:99:12: '**'
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
			// src/edu/kit/iti/algover/parser/Dafny.g:100:3: ( '<' )
			// src/edu/kit/iti/algover/parser/Dafny.g:100:5: '<'
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
			// src/edu/kit/iti/algover/parser/Dafny.g:101:3: ( '<=' )
			// src/edu/kit/iti/algover/parser/Dafny.g:101:5: '<='
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
			// src/edu/kit/iti/algover/parser/Dafny.g:102:3: ( '>' )
			// src/edu/kit/iti/algover/parser/Dafny.g:102:5: '>'
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
			// src/edu/kit/iti/algover/parser/Dafny.g:103:3: ( '>=' )
			// src/edu/kit/iti/algover/parser/Dafny.g:103:5: '>='
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
			// src/edu/kit/iti/algover/parser/Dafny.g:104:3: ( '==' )
			// src/edu/kit/iti/algover/parser/Dafny.g:104:5: '=='
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

	// $ANTLR start "NEQ"
	public final void mNEQ() throws RecognitionException {
		try {
			int _type = NEQ;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// src/edu/kit/iti/algover/parser/Dafny.g:105:4: ( '!=' )
			// src/edu/kit/iti/algover/parser/Dafny.g:105:6: '!='
			{
			match("!="); 

			}

			state.type = _type;
			state.channel = _channel;
		}
		finally {
			// do for sure before leaving
		}
	}
	// $ANTLR end "NEQ"

	// $ANTLR start "DOT"
	public final void mDOT() throws RecognitionException {
		try {
			int _type = DOT;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// src/edu/kit/iti/algover/parser/Dafny.g:106:4: ( '.' )
			// src/edu/kit/iti/algover/parser/Dafny.g:106:6: '.'
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
			// src/edu/kit/iti/algover/parser/Dafny.g:107:12: ( '{' )
			// src/edu/kit/iti/algover/parser/Dafny.g:107:14: '{'
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
			// src/edu/kit/iti/algover/parser/Dafny.g:108:10: ( '}' )
			// src/edu/kit/iti/algover/parser/Dafny.g:108:12: '}'
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
			// src/edu/kit/iti/algover/parser/Dafny.g:110:7: ( 'Length' ( '0' .. '9' )* )
			// src/edu/kit/iti/algover/parser/Dafny.g:110:9: 'Length' ( '0' .. '9' )*
			{
			match("Length"); 

			// src/edu/kit/iti/algover/parser/Dafny.g:110:18: ( '0' .. '9' )*
			loop1:
			while (true) {
				int alt1=2;
				int LA1_0 = input.LA(1);
				if ( ((LA1_0 >= '0' && LA1_0 <= '9')) ) {
					alt1=1;
				}

				switch (alt1) {
				case 1 :
					// src/edu/kit/iti/algover/parser/Dafny.g:
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
			// src/edu/kit/iti/algover/parser/Dafny.g:111:7: ( 'array' ( ( '1' .. '9' ) ( '0' .. '9' )* )? )
			// src/edu/kit/iti/algover/parser/Dafny.g:111:9: 'array' ( ( '1' .. '9' ) ( '0' .. '9' )* )?
			{
			match("array"); 

			// src/edu/kit/iti/algover/parser/Dafny.g:111:17: ( ( '1' .. '9' ) ( '0' .. '9' )* )?
			int alt3=2;
			int LA3_0 = input.LA(1);
			if ( ((LA3_0 >= '1' && LA3_0 <= '9')) ) {
				alt3=1;
			}
			switch (alt3) {
				case 1 :
					// src/edu/kit/iti/algover/parser/Dafny.g:111:18: ( '1' .. '9' ) ( '0' .. '9' )*
					{
					if ( (input.LA(1) >= '1' && input.LA(1) <= '9') ) {
						input.consume();
					}
					else {
						MismatchedSetException mse = new MismatchedSetException(null,input);
						recover(mse);
						throw mse;
					}
					// src/edu/kit/iti/algover/parser/Dafny.g:111:31: ( '0' .. '9' )*
					loop2:
					while (true) {
						int alt2=2;
						int LA2_0 = input.LA(1);
						if ( ((LA2_0 >= '0' && LA2_0 <= '9')) ) {
							alt2=1;
						}

						switch (alt2) {
						case 1 :
							// src/edu/kit/iti/algover/parser/Dafny.g:
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
			// src/edu/kit/iti/algover/parser/Dafny.g:112:4: ( ( 'a' .. 'z' | 'A' .. 'Z' | '_' ) ( 'a' .. 'z' | 'A' .. 'Z' | '0' .. '9' | '_' )* )
			// src/edu/kit/iti/algover/parser/Dafny.g:112:6: ( 'a' .. 'z' | 'A' .. 'Z' | '_' ) ( 'a' .. 'z' | 'A' .. 'Z' | '0' .. '9' | '_' )*
			{
			if ( (input.LA(1) >= 'A' && input.LA(1) <= 'Z')||input.LA(1)=='_'||(input.LA(1) >= 'a' && input.LA(1) <= 'z') ) {
				input.consume();
			}
			else {
				MismatchedSetException mse = new MismatchedSetException(null,input);
				recover(mse);
				throw mse;
			}
			// src/edu/kit/iti/algover/parser/Dafny.g:112:38: ( 'a' .. 'z' | 'A' .. 'Z' | '0' .. '9' | '_' )*
			loop4:
			while (true) {
				int alt4=2;
				int LA4_0 = input.LA(1);
				if ( ((LA4_0 >= '0' && LA4_0 <= '9')||(LA4_0 >= 'A' && LA4_0 <= 'Z')||LA4_0=='_'||(LA4_0 >= 'a' && LA4_0 <= 'z')) ) {
					alt4=1;
				}

				switch (alt4) {
				case 1 :
					// src/edu/kit/iti/algover/parser/Dafny.g:
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
			// src/edu/kit/iti/algover/parser/Dafny.g:113:5: ( ( '0' .. '9' )+ )
			// src/edu/kit/iti/algover/parser/Dafny.g:113:7: ( '0' .. '9' )+
			{
			// src/edu/kit/iti/algover/parser/Dafny.g:113:7: ( '0' .. '9' )+
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
					// src/edu/kit/iti/algover/parser/Dafny.g:
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
			// src/edu/kit/iti/algover/parser/Dafny.g:115:4: ( ( ' ' | '\\n' | '\\r' ) )
			// src/edu/kit/iti/algover/parser/Dafny.g:115:6: ( ' ' | '\\n' | '\\r' )
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
			// src/edu/kit/iti/algover/parser/Dafny.g:116:19: ( '//' (~ ( '\\r' | '\\n' ) )* )
			// src/edu/kit/iti/algover/parser/Dafny.g:116:21: '//' (~ ( '\\r' | '\\n' ) )*
			{
			match("//"); 

			// src/edu/kit/iti/algover/parser/Dafny.g:116:26: (~ ( '\\r' | '\\n' ) )*
			loop6:
			while (true) {
				int alt6=2;
				int LA6_0 = input.LA(1);
				if ( ((LA6_0 >= '\u0000' && LA6_0 <= '\t')||(LA6_0 >= '\u000B' && LA6_0 <= '\f')||(LA6_0 >= '\u000E' && LA6_0 <= '\uFFFF')) ) {
					alt6=1;
				}

				switch (alt6) {
				case 1 :
					// src/edu/kit/iti/algover/parser/Dafny.g:
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
			// src/edu/kit/iti/algover/parser/Dafny.g:117:18: ( '/*' ( . )* '*/' )
			// src/edu/kit/iti/algover/parser/Dafny.g:117:20: '/*' ( . )* '*/'
			{
			match("/*"); 

			// src/edu/kit/iti/algover/parser/Dafny.g:117:25: ( . )*
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
					// src/edu/kit/iti/algover/parser/Dafny.g:117:25: .
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
		// src/edu/kit/iti/algover/parser/Dafny.g:1:8: ( T__68 | T__69 | T__70 | T__71 | T__72 | T__73 | T__74 | INT | BOOL | SET | RETURNS | ENSURES | REQUIRES | DECREASES | FUNCTION | METHOD | LEMMA | LABEL | ELSE | IF | THEN | WHILE | VAR | CALL | INVARIANT | ASSERT | ASSUME | MODIFIES | CLASS | THIS | NULL | ALL | EX | DOUBLECOLON | ASSIGN | OR | AND | IMPLIES | PLUS | MINUS | NOT | TIMES | UNION | INTERSECT | LT | LE | GT | GE | EQ | NEQ | DOT | BLOCK_BEGIN | BLOCK_END | LENGTH | ARRAY | ID | LIT | WS | SINGLELINE_COMMENT | MULTILINE_COMMENT )
		int alt8=60;
		alt8 = dfa8.predict(input);
		switch (alt8) {
			case 1 :
				// src/edu/kit/iti/algover/parser/Dafny.g:1:10: T__68
				{
				mT__68(); 

				}
				break;
			case 2 :
				// src/edu/kit/iti/algover/parser/Dafny.g:1:16: T__69
				{
				mT__69(); 

				}
				break;
			case 3 :
				// src/edu/kit/iti/algover/parser/Dafny.g:1:22: T__70
				{
				mT__70(); 

				}
				break;
			case 4 :
				// src/edu/kit/iti/algover/parser/Dafny.g:1:28: T__71
				{
				mT__71(); 

				}
				break;
			case 5 :
				// src/edu/kit/iti/algover/parser/Dafny.g:1:34: T__72
				{
				mT__72(); 

				}
				break;
			case 6 :
				// src/edu/kit/iti/algover/parser/Dafny.g:1:40: T__73
				{
				mT__73(); 

				}
				break;
			case 7 :
				// src/edu/kit/iti/algover/parser/Dafny.g:1:46: T__74
				{
				mT__74(); 

				}
				break;
			case 8 :
				// src/edu/kit/iti/algover/parser/Dafny.g:1:52: INT
				{
				mINT(); 

				}
				break;
			case 9 :
				// src/edu/kit/iti/algover/parser/Dafny.g:1:56: BOOL
				{
				mBOOL(); 

				}
				break;
			case 10 :
				// src/edu/kit/iti/algover/parser/Dafny.g:1:61: SET
				{
				mSET(); 

				}
				break;
			case 11 :
				// src/edu/kit/iti/algover/parser/Dafny.g:1:65: RETURNS
				{
				mRETURNS(); 

				}
				break;
			case 12 :
				// src/edu/kit/iti/algover/parser/Dafny.g:1:73: ENSURES
				{
				mENSURES(); 

				}
				break;
			case 13 :
				// src/edu/kit/iti/algover/parser/Dafny.g:1:81: REQUIRES
				{
				mREQUIRES(); 

				}
				break;
			case 14 :
				// src/edu/kit/iti/algover/parser/Dafny.g:1:90: DECREASES
				{
				mDECREASES(); 

				}
				break;
			case 15 :
				// src/edu/kit/iti/algover/parser/Dafny.g:1:100: FUNCTION
				{
				mFUNCTION(); 

				}
				break;
			case 16 :
				// src/edu/kit/iti/algover/parser/Dafny.g:1:109: METHOD
				{
				mMETHOD(); 

				}
				break;
			case 17 :
				// src/edu/kit/iti/algover/parser/Dafny.g:1:116: LEMMA
				{
				mLEMMA(); 

				}
				break;
			case 18 :
				// src/edu/kit/iti/algover/parser/Dafny.g:1:122: LABEL
				{
				mLABEL(); 

				}
				break;
			case 19 :
				// src/edu/kit/iti/algover/parser/Dafny.g:1:128: ELSE
				{
				mELSE(); 

				}
				break;
			case 20 :
				// src/edu/kit/iti/algover/parser/Dafny.g:1:133: IF
				{
				mIF(); 

				}
				break;
			case 21 :
				// src/edu/kit/iti/algover/parser/Dafny.g:1:136: THEN
				{
				mTHEN(); 

				}
				break;
			case 22 :
				// src/edu/kit/iti/algover/parser/Dafny.g:1:141: WHILE
				{
				mWHILE(); 

				}
				break;
			case 23 :
				// src/edu/kit/iti/algover/parser/Dafny.g:1:147: VAR
				{
				mVAR(); 

				}
				break;
			case 24 :
				// src/edu/kit/iti/algover/parser/Dafny.g:1:151: CALL
				{
				mCALL(); 

				}
				break;
			case 25 :
				// src/edu/kit/iti/algover/parser/Dafny.g:1:156: INVARIANT
				{
				mINVARIANT(); 

				}
				break;
			case 26 :
				// src/edu/kit/iti/algover/parser/Dafny.g:1:166: ASSERT
				{
				mASSERT(); 

				}
				break;
			case 27 :
				// src/edu/kit/iti/algover/parser/Dafny.g:1:173: ASSUME
				{
				mASSUME(); 

				}
				break;
			case 28 :
				// src/edu/kit/iti/algover/parser/Dafny.g:1:180: MODIFIES
				{
				mMODIFIES(); 

				}
				break;
			case 29 :
				// src/edu/kit/iti/algover/parser/Dafny.g:1:189: CLASS
				{
				mCLASS(); 

				}
				break;
			case 30 :
				// src/edu/kit/iti/algover/parser/Dafny.g:1:195: THIS
				{
				mTHIS(); 

				}
				break;
			case 31 :
				// src/edu/kit/iti/algover/parser/Dafny.g:1:200: NULL
				{
				mNULL(); 

				}
				break;
			case 32 :
				// src/edu/kit/iti/algover/parser/Dafny.g:1:205: ALL
				{
				mALL(); 

				}
				break;
			case 33 :
				// src/edu/kit/iti/algover/parser/Dafny.g:1:209: EX
				{
				mEX(); 

				}
				break;
			case 34 :
				// src/edu/kit/iti/algover/parser/Dafny.g:1:212: DOUBLECOLON
				{
				mDOUBLECOLON(); 

				}
				break;
			case 35 :
				// src/edu/kit/iti/algover/parser/Dafny.g:1:224: ASSIGN
				{
				mASSIGN(); 

				}
				break;
			case 36 :
				// src/edu/kit/iti/algover/parser/Dafny.g:1:231: OR
				{
				mOR(); 

				}
				break;
			case 37 :
				// src/edu/kit/iti/algover/parser/Dafny.g:1:234: AND
				{
				mAND(); 

				}
				break;
			case 38 :
				// src/edu/kit/iti/algover/parser/Dafny.g:1:238: IMPLIES
				{
				mIMPLIES(); 

				}
				break;
			case 39 :
				// src/edu/kit/iti/algover/parser/Dafny.g:1:246: PLUS
				{
				mPLUS(); 

				}
				break;
			case 40 :
				// src/edu/kit/iti/algover/parser/Dafny.g:1:251: MINUS
				{
				mMINUS(); 

				}
				break;
			case 41 :
				// src/edu/kit/iti/algover/parser/Dafny.g:1:257: NOT
				{
				mNOT(); 

				}
				break;
			case 42 :
				// src/edu/kit/iti/algover/parser/Dafny.g:1:261: TIMES
				{
				mTIMES(); 

				}
				break;
			case 43 :
				// src/edu/kit/iti/algover/parser/Dafny.g:1:267: UNION
				{
				mUNION(); 

				}
				break;
			case 44 :
				// src/edu/kit/iti/algover/parser/Dafny.g:1:273: INTERSECT
				{
				mINTERSECT(); 

				}
				break;
			case 45 :
				// src/edu/kit/iti/algover/parser/Dafny.g:1:283: LT
				{
				mLT(); 

				}
				break;
			case 46 :
				// src/edu/kit/iti/algover/parser/Dafny.g:1:286: LE
				{
				mLE(); 

				}
				break;
			case 47 :
				// src/edu/kit/iti/algover/parser/Dafny.g:1:289: GT
				{
				mGT(); 

				}
				break;
			case 48 :
				// src/edu/kit/iti/algover/parser/Dafny.g:1:292: GE
				{
				mGE(); 

				}
				break;
			case 49 :
				// src/edu/kit/iti/algover/parser/Dafny.g:1:295: EQ
				{
				mEQ(); 

				}
				break;
			case 50 :
				// src/edu/kit/iti/algover/parser/Dafny.g:1:298: NEQ
				{
				mNEQ(); 

				}
				break;
			case 51 :
				// src/edu/kit/iti/algover/parser/Dafny.g:1:302: DOT
				{
				mDOT(); 

				}
				break;
			case 52 :
				// src/edu/kit/iti/algover/parser/Dafny.g:1:306: BLOCK_BEGIN
				{
				mBLOCK_BEGIN(); 

				}
				break;
			case 53 :
				// src/edu/kit/iti/algover/parser/Dafny.g:1:318: BLOCK_END
				{
				mBLOCK_END(); 

				}
				break;
			case 54 :
				// src/edu/kit/iti/algover/parser/Dafny.g:1:328: LENGTH
				{
				mLENGTH(); 

				}
				break;
			case 55 :
				// src/edu/kit/iti/algover/parser/Dafny.g:1:335: ARRAY
				{
				mARRAY(); 

				}
				break;
			case 56 :
				// src/edu/kit/iti/algover/parser/Dafny.g:1:341: ID
				{
				mID(); 

				}
				break;
			case 57 :
				// src/edu/kit/iti/algover/parser/Dafny.g:1:344: LIT
				{
				mLIT(); 

				}
				break;
			case 58 :
				// src/edu/kit/iti/algover/parser/Dafny.g:1:348: WS
				{
				mWS(); 

				}
				break;
			case 59 :
				// src/edu/kit/iti/algover/parser/Dafny.g:1:351: SINGLELINE_COMMENT
				{
				mSINGLELINE_COMMENT(); 

				}
				break;
			case 60 :
				// src/edu/kit/iti/algover/parser/Dafny.g:1:370: MULTILINE_COMMENT
				{
				mMULTILINE_COMMENT(); 

				}
				break;

		}
	}


	protected DFA8 dfa8 = new DFA8(this);
	static final String DFA8_eotS =
		"\4\uffff\1\52\3\uffff\17\44\3\uffff\1\104\1\uffff\1\106\1\110\1\112\1"+
		"\114\3\uffff\1\44\7\uffff\1\44\1\122\25\44\1\153\12\uffff\1\44\2\uffff"+
		"\1\155\1\44\1\uffff\1\44\1\160\17\44\1\u0080\5\44\2\uffff\1\44\1\uffff"+
		"\1\44\1\u0089\1\uffff\3\44\1\u008d\10\44\1\u0096\1\u0097\1\44\1\uffff"+
		"\1\u0099\4\44\1\u009e\2\44\1\uffff\3\44\1\uffff\6\44\1\u00aa\1\u00ab\2"+
		"\uffff\1\u00ac\1\uffff\1\u00ad\2\44\1\u00b1\1\uffff\5\44\1\u00b7\2\44"+
		"\1\u00ba\1\u00bb\1\44\4\uffff\1\u00bd\1\u00be\1\u00b1\1\uffff\1\u00c1"+
		"\1\44\1\u00c3\1\44\1\u00c5\1\uffff\2\44\2\uffff\1\44\2\uffff\1\u00b1\1"+
		"\u00c1\1\uffff\1\44\1\uffff\1\u00ca\1\uffff\1\44\1\u00cc\1\u00cd\1\u00ce"+
		"\1\uffff\1\u00cf\4\uffff";
	static final String DFA8_eofS =
		"\u00d0\uffff";
	static final String DFA8_minS =
		"\1\12\3\uffff\1\72\3\uffff\1\146\1\157\2\145\1\154\1\145\1\157\1\145\1"+
		"\141\2\150\2\141\1\162\1\165\2\uffff\1\75\1\53\1\uffff\1\75\1\52\2\75"+
		"\3\uffff\1\145\3\uffff\1\52\3\uffff\1\164\1\60\1\157\1\164\1\161\2\163"+
		"\1\151\1\143\1\156\1\162\1\164\1\144\1\155\1\142\1\145\1\151\1\162\1\154"+
		"\1\141\1\163\1\162\1\154\1\76\12\uffff\1\156\2\uffff\1\60\1\141\1\uffff"+
		"\1\154\1\60\3\165\1\145\1\163\1\162\1\143\1\141\1\150\1\151\1\155\1\145"+
		"\1\156\1\163\1\154\1\60\1\154\1\163\1\145\1\141\1\154\2\uffff\1\147\1"+
		"\uffff\1\162\1\60\1\uffff\1\162\1\151\1\162\1\60\1\164\1\145\1\164\1\154"+
		"\1\157\1\146\1\141\1\154\2\60\1\145\1\uffff\1\60\1\163\1\162\1\155\1\171"+
		"\1\60\1\164\1\151\1\uffff\1\156\1\162\1\145\1\uffff\1\163\1\141\1\151"+
		"\1\154\1\144\1\151\2\60\2\uffff\1\60\1\uffff\1\60\1\164\1\145\1\60\1\uffff"+
		"\1\150\1\141\1\163\1\145\1\163\1\60\1\163\1\157\2\60\1\145\4\uffff\3\60"+
		"\1\uffff\1\60\1\156\1\60\1\163\1\60\1\uffff\1\145\1\156\2\uffff\1\163"+
		"\2\uffff\2\60\1\uffff\1\164\1\uffff\1\60\1\uffff\1\163\3\60\1\uffff\1"+
		"\60\4\uffff";
	static final String DFA8_maxS =
		"\1\175\3\uffff\1\75\3\uffff\1\156\1\157\2\145\1\170\1\145\1\165\1\157"+
		"\1\145\2\150\1\141\1\154\1\163\1\165\2\uffff\1\75\1\53\1\uffff\1\75\1"+
		"\52\2\75\3\uffff\1\145\3\uffff\1\57\3\uffff\1\166\1\172\1\157\2\164\2"+
		"\163\1\151\1\143\1\156\1\162\1\164\1\144\1\155\1\142\2\151\1\162\1\154"+
		"\1\141\1\163\1\162\1\154\1\76\12\uffff\1\156\2\uffff\1\172\1\141\1\uffff"+
		"\1\154\1\172\3\165\1\145\1\163\1\162\1\143\1\141\1\150\1\151\1\155\1\145"+
		"\1\156\1\163\1\154\1\172\1\154\1\163\1\165\1\141\1\154\2\uffff\1\147\1"+
		"\uffff\1\162\1\172\1\uffff\1\162\1\151\1\162\1\172\1\164\1\145\1\164\1"+
		"\154\1\157\1\146\1\141\1\154\2\172\1\145\1\uffff\1\172\1\163\1\162\1\155"+
		"\1\171\1\172\1\164\1\151\1\uffff\1\156\1\162\1\145\1\uffff\1\163\1\141"+
		"\1\151\1\154\1\144\1\151\2\172\2\uffff\1\172\1\uffff\1\172\1\164\1\145"+
		"\1\172\1\uffff\1\150\1\141\1\163\1\145\1\163\1\172\1\163\1\157\2\172\1"+
		"\145\4\uffff\3\172\1\uffff\1\172\1\156\1\172\1\163\1\172\1\uffff\1\145"+
		"\1\156\2\uffff\1\163\2\uffff\2\172\1\uffff\1\164\1\uffff\1\172\1\uffff"+
		"\1\163\3\172\1\uffff\1\172\4\uffff";
	static final String DFA8_acceptS =
		"\1\uffff\1\1\1\2\1\3\1\uffff\1\5\1\6\1\7\17\uffff\1\44\1\45\2\uffff\1"+
		"\50\4\uffff\1\63\1\64\1\65\1\uffff\1\70\1\71\1\72\1\uffff\1\42\1\43\1"+
		"\4\30\uffff\1\53\1\47\1\62\1\51\1\54\1\52\1\56\1\55\1\60\1\57\1\uffff"+
		"\1\73\1\74\2\uffff\1\24\27\uffff\1\46\1\61\1\uffff\1\10\2\uffff\1\12\17"+
		"\uffff\1\27\10\uffff\1\11\3\uffff\1\23\10\uffff\1\25\1\36\1\uffff\1\30"+
		"\4\uffff\1\37\13\uffff\1\21\1\22\1\26\1\35\3\uffff\1\67\5\uffff\1\41\2"+
		"\uffff\1\40\1\20\1\uffff\1\32\1\33\2\uffff\1\66\1\uffff\1\13\1\uffff\1"+
		"\14\4\uffff\1\15\1\uffff\1\17\1\34\1\31\1\16";
	static final String DFA8_specialS =
		"\u00d0\uffff}>";
	static final String[] DFA8_transitionS = {
			"\1\46\2\uffff\1\46\22\uffff\1\46\1\34\4\uffff\1\30\1\uffff\1\1\1\2\1"+
			"\35\1\32\1\3\1\33\1\40\1\47\12\45\1\4\1\5\1\36\1\31\1\37\2\uffff\13\44"+
			"\1\43\16\44\1\6\1\uffff\1\7\1\uffff\1\44\1\uffff\1\25\1\11\1\24\1\15"+
			"\1\14\1\16\2\44\1\10\2\44\1\20\1\17\1\26\3\44\1\13\1\12\1\21\1\44\1\23"+
			"\1\22\3\44\1\41\1\27\1\42",
			"",
			"",
			"",
			"\1\50\2\uffff\1\51",
			"",
			"",
			"",
			"\1\54\7\uffff\1\53",
			"\1\55",
			"\1\56",
			"\1\57",
			"\1\61\1\uffff\1\60\11\uffff\1\62",
			"\1\63",
			"\1\65\5\uffff\1\64",
			"\1\66\11\uffff\1\67",
			"\1\71\3\uffff\1\70",
			"\1\72",
			"\1\73",
			"\1\74",
			"\1\75\12\uffff\1\76",
			"\1\100\1\77",
			"\1\101",
			"",
			"",
			"\1\102",
			"\1\103",
			"",
			"\1\105",
			"\1\107",
			"\1\111",
			"\1\113",
			"",
			"",
			"",
			"\1\115",
			"",
			"",
			"",
			"\1\117\4\uffff\1\116",
			"",
			"",
			"",
			"\1\120\1\uffff\1\121",
			"\12\44\7\uffff\32\44\4\uffff\1\44\1\uffff\32\44",
			"\1\123",
			"\1\124",
			"\1\126\2\uffff\1\125",
			"\1\127",
			"\1\130",
			"\1\131",
			"\1\132",
			"\1\133",
			"\1\134",
			"\1\135",
			"\1\136",
			"\1\137",
			"\1\140",
			"\1\141\3\uffff\1\142",
			"\1\143",
			"\1\144",
			"\1\145",
			"\1\146",
			"\1\147",
			"\1\150",
			"\1\151",
			"\1\152",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"\1\154",
			"",
			"",
			"\12\44\7\uffff\32\44\4\uffff\1\44\1\uffff\32\44",
			"\1\156",
			"",
			"\1\157",
			"\12\44\7\uffff\32\44\4\uffff\1\44\1\uffff\32\44",
			"\1\161",
			"\1\162",
			"\1\163",
			"\1\164",
			"\1\165",
			"\1\166",
			"\1\167",
			"\1\170",
			"\1\171",
			"\1\172",
			"\1\173",
			"\1\174",
			"\1\175",
			"\1\176",
			"\1\177",
			"\12\44\7\uffff\32\44\4\uffff\1\44\1\uffff\32\44",
			"\1\u0081",
			"\1\u0082",
			"\1\u0083\17\uffff\1\u0084",
			"\1\u0085",
			"\1\u0086",
			"",
			"",
			"\1\u0087",
			"",
			"\1\u0088",
			"\12\44\7\uffff\32\44\4\uffff\1\44\1\uffff\32\44",
			"",
			"\1\u008a",
			"\1\u008b",
			"\1\u008c",
			"\12\44\7\uffff\32\44\4\uffff\1\44\1\uffff\32\44",
			"\1\u008e",
			"\1\u008f",
			"\1\u0090",
			"\1\u0091",
			"\1\u0092",
			"\1\u0093",
			"\1\u0094",
			"\1\u0095",
			"\12\44\7\uffff\32\44\4\uffff\1\44\1\uffff\32\44",
			"\12\44\7\uffff\32\44\4\uffff\1\44\1\uffff\32\44",
			"\1\u0098",
			"",
			"\12\44\7\uffff\32\44\4\uffff\1\44\1\uffff\32\44",
			"\1\u009a",
			"\1\u009b",
			"\1\u009c",
			"\1\u009d",
			"\12\44\7\uffff\32\44\4\uffff\1\44\1\uffff\32\44",
			"\1\u009f",
			"\1\u00a0",
			"",
			"\1\u00a1",
			"\1\u00a2",
			"\1\u00a3",
			"",
			"\1\u00a4",
			"\1\u00a5",
			"\1\u00a6",
			"\1\u00a7",
			"\1\u00a8",
			"\1\u00a9",
			"\12\44\7\uffff\32\44\4\uffff\1\44\1\uffff\32\44",
			"\12\44\7\uffff\32\44\4\uffff\1\44\1\uffff\32\44",
			"",
			"",
			"\12\44\7\uffff\32\44\4\uffff\1\44\1\uffff\32\44",
			"",
			"\12\44\7\uffff\32\44\4\uffff\1\44\1\uffff\32\44",
			"\1\u00ae",
			"\1\u00af",
			"\1\44\11\u00b0\7\uffff\32\44\4\uffff\1\44\1\uffff\32\44",
			"",
			"\1\u00b2",
			"\1\u00b3",
			"\1\u00b4",
			"\1\u00b5",
			"\1\u00b6",
			"\12\44\7\uffff\32\44\4\uffff\1\44\1\uffff\32\44",
			"\1\u00b8",
			"\1\u00b9",
			"\12\44\7\uffff\32\44\4\uffff\1\44\1\uffff\32\44",
			"\12\44\7\uffff\32\44\4\uffff\1\44\1\uffff\32\44",
			"\1\u00bc",
			"",
			"",
			"",
			"",
			"\12\44\7\uffff\32\44\4\uffff\1\44\1\uffff\32\44",
			"\12\44\7\uffff\32\44\4\uffff\1\44\1\uffff\32\44",
			"\12\u00bf\7\uffff\32\44\4\uffff\1\44\1\uffff\32\44",
			"",
			"\12\u00c0\7\uffff\32\44\4\uffff\1\44\1\uffff\32\44",
			"\1\u00c2",
			"\12\44\7\uffff\32\44\4\uffff\1\44\1\uffff\32\44",
			"\1\u00c4",
			"\12\44\7\uffff\32\44\4\uffff\1\44\1\uffff\32\44",
			"",
			"\1\u00c6",
			"\1\u00c7",
			"",
			"",
			"\1\u00c8",
			"",
			"",
			"\12\u00bf\7\uffff\32\44\4\uffff\1\44\1\uffff\32\44",
			"\12\u00c0\7\uffff\32\44\4\uffff\1\44\1\uffff\32\44",
			"",
			"\1\u00c9",
			"",
			"\12\44\7\uffff\32\44\4\uffff\1\44\1\uffff\32\44",
			"",
			"\1\u00cb",
			"\12\44\7\uffff\32\44\4\uffff\1\44\1\uffff\32\44",
			"\12\44\7\uffff\32\44\4\uffff\1\44\1\uffff\32\44",
			"\12\44\7\uffff\32\44\4\uffff\1\44\1\uffff\32\44",
			"",
			"\12\44\7\uffff\32\44\4\uffff\1\44\1\uffff\32\44",
			"",
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
			return "1:1: Tokens : ( T__68 | T__69 | T__70 | T__71 | T__72 | T__73 | T__74 | INT | BOOL | SET | RETURNS | ENSURES | REQUIRES | DECREASES | FUNCTION | METHOD | LEMMA | LABEL | ELSE | IF | THEN | WHILE | VAR | CALL | INVARIANT | ASSERT | ASSUME | MODIFIES | CLASS | THIS | NULL | ALL | EX | DOUBLECOLON | ASSIGN | OR | AND | IMPLIES | PLUS | MINUS | NOT | TIMES | UNION | INTERSECT | LT | LE | GT | GE | EQ | NEQ | DOT | BLOCK_BEGIN | BLOCK_END | LENGTH | ARRAY | ID | LIT | WS | SINGLELINE_COMMENT | MULTILINE_COMMENT );";
		}
	}

}
