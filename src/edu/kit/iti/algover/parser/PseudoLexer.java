// $ANTLR 3.5.1 Pseudo.g 2015-09-10 12:11:29

  package edu.kit.iti.algover.parser;


import org.antlr.runtime.*;
import java.util.Stack;
import java.util.List;
import java.util.ArrayList;

@SuppressWarnings("all")
public class PseudoLexer extends Lexer {
	public static final int EOF=-1;
	public static final int T__51=51;
	public static final int T__52=52;
	public static final int T__53=53;
	public static final int T__54=54;
	public static final int T__55=55;
	public static final int T__56=56;
	public static final int T__57=57;
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
	public static final int LE=30;
	public static final int LENGTH=31;
	public static final int LISTEX=32;
	public static final int LIT=33;
	public static final int LT=34;
	public static final int METHOD=35;
	public static final int MINUS=36;
	public static final int NOT=37;
	public static final int OR=38;
	public static final int PLUS=39;
	public static final int REQUIRES=40;
	public static final int RESULTS=41;
	public static final int RETURNS=42;
	public static final int SET=43;
	public static final int SETEX=44;
	public static final int THEN=45;
	public static final int TIMES=46;
	public static final int UNION=47;
	public static final int VAR=48;
	public static final int WHILE=49;
	public static final int WS=50;

	// delegates
	// delegators
	public Lexer[] getDelegates() {
		return new Lexer[] {};
	}

	public PseudoLexer() {} 
	public PseudoLexer(CharStream input) {
		this(input, new RecognizerSharedState());
	}
	public PseudoLexer(CharStream input, RecognizerSharedState state) {
		super(input,state);
	}
	@Override public String getGrammarFileName() { return "Pseudo.g"; }

	// $ANTLR start "T__51"
	public final void mT__51() throws RecognitionException {
		try {
			int _type = T__51;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// Pseudo.g:6:7: ( '(' )
			// Pseudo.g:6:9: '('
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
	// $ANTLR end "T__51"

	// $ANTLR start "T__52"
	public final void mT__52() throws RecognitionException {
		try {
			int _type = T__52;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// Pseudo.g:7:7: ( ')' )
			// Pseudo.g:7:9: ')'
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
	// $ANTLR end "T__52"

	// $ANTLR start "T__53"
	public final void mT__53() throws RecognitionException {
		try {
			int _type = T__53;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// Pseudo.g:8:7: ( ',' )
			// Pseudo.g:8:9: ','
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
	// $ANTLR end "T__53"

	// $ANTLR start "T__54"
	public final void mT__54() throws RecognitionException {
		try {
			int _type = T__54;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// Pseudo.g:9:7: ( ':' )
			// Pseudo.g:9:9: ':'
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
	// $ANTLR end "T__54"

	// $ANTLR start "T__55"
	public final void mT__55() throws RecognitionException {
		try {
			int _type = T__55;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// Pseudo.g:10:7: ( ';' )
			// Pseudo.g:10:9: ';'
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
	// $ANTLR end "T__55"

	// $ANTLR start "T__56"
	public final void mT__56() throws RecognitionException {
		try {
			int _type = T__56;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// Pseudo.g:11:7: ( '[' )
			// Pseudo.g:11:9: '['
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
	// $ANTLR end "T__56"

	// $ANTLR start "T__57"
	public final void mT__57() throws RecognitionException {
		try {
			int _type = T__57;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// Pseudo.g:12:7: ( ']' )
			// Pseudo.g:12:9: ']'
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
	// $ANTLR end "T__57"

	// $ANTLR start "INT"
	public final void mINT() throws RecognitionException {
		try {
			int _type = INT;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// Pseudo.g:56:5: ( 'int' )
			// Pseudo.g:56:7: 'int'
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
			// Pseudo.g:57:5: ( 'set' )
			// Pseudo.g:57:7: 'set'
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
			// Pseudo.g:58:9: ( 'returns' )
			// Pseudo.g:58:11: 'returns'
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
			// Pseudo.g:59:8: ( 'ensures' )
			// Pseudo.g:59:10: 'ensures'
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
			// Pseudo.g:60:9: ( 'requires' )
			// Pseudo.g:60:11: 'requires'
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
			// Pseudo.g:61:10: ( 'decreases' )
			// Pseudo.g:61:12: 'decreases'
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
			// Pseudo.g:62:7: ( 'method' )
			// Pseudo.g:62:9: 'method'
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

	// $ANTLR start "ELSE"
	public final void mELSE() throws RecognitionException {
		try {
			int _type = ELSE;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// Pseudo.g:63:5: ( 'else' )
			// Pseudo.g:63:7: 'else'
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
			// Pseudo.g:64:3: ( 'if' )
			// Pseudo.g:64:5: 'if'
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
			// Pseudo.g:65:5: ( 'then' )
			// Pseudo.g:65:7: 'then'
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
			// Pseudo.g:66:6: ( 'while' )
			// Pseudo.g:66:8: 'while'
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
			// Pseudo.g:67:4: ( 'var' )
			// Pseudo.g:67:6: 'var'
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
			// Pseudo.g:68:5: ( 'call' )
			// Pseudo.g:68:6: 'call'
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
			// Pseudo.g:69:10: ( 'invariant' )
			// Pseudo.g:69:12: 'invariant'
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
			// Pseudo.g:70:7: ( 'assert' )
			// Pseudo.g:70:9: 'assert'
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

	// $ANTLR start "LENGTH"
	public final void mLENGTH() throws RecognitionException {
		try {
			int _type = LENGTH;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// Pseudo.g:71:7: ( 'length' )
			// Pseudo.g:71:9: 'length'
			{
			match("length"); 

			}

			state.type = _type;
			state.channel = _channel;
		}
		finally {
			// do for sure before leaving
		}
	}
	// $ANTLR end "LENGTH"

	// $ANTLR start "ALL"
	public final void mALL() throws RecognitionException {
		try {
			int _type = ALL;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// Pseudo.g:73:4: ( 'forall' )
			// Pseudo.g:73:6: 'forall'
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
			// Pseudo.g:74:3: ( 'exists' )
			// Pseudo.g:74:5: 'exists'
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
			// Pseudo.g:76:12: ( '::' )
			// Pseudo.g:76:14: '::'
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
			// Pseudo.g:77:7: ( ':=' )
			// Pseudo.g:77:9: ':='
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
			// Pseudo.g:78:3: ( '||' )
			// Pseudo.g:78:5: '||'
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
			// Pseudo.g:79:4: ( '&&' )
			// Pseudo.g:79:6: '&&'
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
			// Pseudo.g:80:8: ( '==>' )
			// Pseudo.g:80:10: '==>'
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
			// Pseudo.g:81:5: ( '+' )
			// Pseudo.g:81:7: '+'
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
			// Pseudo.g:82:6: ( '-' )
			// Pseudo.g:82:8: '-'
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
			// Pseudo.g:83:4: ( '!' )
			// Pseudo.g:83:6: '!'
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
			// Pseudo.g:84:6: ( '*' )
			// Pseudo.g:84:8: '*'
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
			// Pseudo.g:85:6: ( '++' )
			// Pseudo.g:85:8: '++'
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
			// Pseudo.g:86:10: ( '**' )
			// Pseudo.g:86:12: '**'
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
			// Pseudo.g:87:3: ( '<' )
			// Pseudo.g:87:5: '<'
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
			// Pseudo.g:88:3: ( '<=' )
			// Pseudo.g:88:5: '<='
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
			// Pseudo.g:89:3: ( '>' )
			// Pseudo.g:89:5: '>'
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
			// Pseudo.g:90:3: ( '>=' )
			// Pseudo.g:90:5: '>='
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
			// Pseudo.g:91:3: ( '==' )
			// Pseudo.g:91:5: '=='
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
			// Pseudo.g:92:4: ( '.' )
			// Pseudo.g:92:6: '.'
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
			// Pseudo.g:94:12: ( '{' )
			// Pseudo.g:94:14: '{'
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
			// Pseudo.g:95:10: ( '}' )
			// Pseudo.g:95:12: '}'
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

	// $ANTLR start "ARRAY"
	public final void mARRAY() throws RecognitionException {
		try {
			int _type = ARRAY;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// Pseudo.g:98:7: ( 'array' ( ( '1' .. '9' ) ( '0' .. '9' )* )? )
			// Pseudo.g:98:9: 'array' ( ( '1' .. '9' ) ( '0' .. '9' )* )?
			{
			match("array"); 

			// Pseudo.g:98:17: ( ( '1' .. '9' ) ( '0' .. '9' )* )?
			int alt2=2;
			int LA2_0 = input.LA(1);
			if ( ((LA2_0 >= '1' && LA2_0 <= '9')) ) {
				alt2=1;
			}
			switch (alt2) {
				case 1 :
					// Pseudo.g:98:18: ( '1' .. '9' ) ( '0' .. '9' )*
					{
					if ( (input.LA(1) >= '1' && input.LA(1) <= '9') ) {
						input.consume();
					}
					else {
						MismatchedSetException mse = new MismatchedSetException(null,input);
						recover(mse);
						throw mse;
					}
					// Pseudo.g:98:31: ( '0' .. '9' )*
					loop1:
					while (true) {
						int alt1=2;
						int LA1_0 = input.LA(1);
						if ( ((LA1_0 >= '0' && LA1_0 <= '9')) ) {
							alt1=1;
						}

						switch (alt1) {
						case 1 :
							// Pseudo.g:
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
			// Pseudo.g:99:4: ( ( 'a' .. 'z' | 'A' .. 'Z' | '_' )+ )
			// Pseudo.g:99:6: ( 'a' .. 'z' | 'A' .. 'Z' | '_' )+
			{
			// Pseudo.g:99:6: ( 'a' .. 'z' | 'A' .. 'Z' | '_' )+
			int cnt3=0;
			loop3:
			while (true) {
				int alt3=2;
				int LA3_0 = input.LA(1);
				if ( ((LA3_0 >= 'A' && LA3_0 <= 'Z')||LA3_0=='_'||(LA3_0 >= 'a' && LA3_0 <= 'z')) ) {
					alt3=1;
				}

				switch (alt3) {
				case 1 :
					// Pseudo.g:
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
					if ( cnt3 >= 1 ) break loop3;
					EarlyExitException eee = new EarlyExitException(3, input);
					throw eee;
				}
				cnt3++;
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
			// Pseudo.g:100:5: ( ( '0' .. '9' )+ )
			// Pseudo.g:100:7: ( '0' .. '9' )+
			{
			// Pseudo.g:100:7: ( '0' .. '9' )+
			int cnt4=0;
			loop4:
			while (true) {
				int alt4=2;
				int LA4_0 = input.LA(1);
				if ( ((LA4_0 >= '0' && LA4_0 <= '9')) ) {
					alt4=1;
				}

				switch (alt4) {
				case 1 :
					// Pseudo.g:
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
	// $ANTLR end "LIT"

	// $ANTLR start "WS"
	public final void mWS() throws RecognitionException {
		try {
			int _type = WS;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// Pseudo.g:101:4: ( ( ' ' | '\\n' | '\\r' ) )
			// Pseudo.g:101:6: ( ' ' | '\\n' | '\\r' )
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
		// Pseudo.g:1:8: ( T__51 | T__52 | T__53 | T__54 | T__55 | T__56 | T__57 | INT | SET | RETURNS | ENSURES | REQUIRES | DECREASES | METHOD | ELSE | IF | THEN | WHILE | VAR | CALL | INVARIANT | ASSERT | LENGTH | ALL | EX | DOUBLECOLON | ASSIGN | OR | AND | IMPLIES | PLUS | MINUS | NOT | TIMES | UNION | INTERSECT | LT | LE | GT | GE | EQ | DOT | BLOCK_BEGIN | BLOCK_END | ARRAY | ID | LIT | WS )
		int alt5=48;
		alt5 = dfa5.predict(input);
		switch (alt5) {
			case 1 :
				// Pseudo.g:1:10: T__51
				{
				mT__51(); 

				}
				break;
			case 2 :
				// Pseudo.g:1:16: T__52
				{
				mT__52(); 

				}
				break;
			case 3 :
				// Pseudo.g:1:22: T__53
				{
				mT__53(); 

				}
				break;
			case 4 :
				// Pseudo.g:1:28: T__54
				{
				mT__54(); 

				}
				break;
			case 5 :
				// Pseudo.g:1:34: T__55
				{
				mT__55(); 

				}
				break;
			case 6 :
				// Pseudo.g:1:40: T__56
				{
				mT__56(); 

				}
				break;
			case 7 :
				// Pseudo.g:1:46: T__57
				{
				mT__57(); 

				}
				break;
			case 8 :
				// Pseudo.g:1:52: INT
				{
				mINT(); 

				}
				break;
			case 9 :
				// Pseudo.g:1:56: SET
				{
				mSET(); 

				}
				break;
			case 10 :
				// Pseudo.g:1:60: RETURNS
				{
				mRETURNS(); 

				}
				break;
			case 11 :
				// Pseudo.g:1:68: ENSURES
				{
				mENSURES(); 

				}
				break;
			case 12 :
				// Pseudo.g:1:76: REQUIRES
				{
				mREQUIRES(); 

				}
				break;
			case 13 :
				// Pseudo.g:1:85: DECREASES
				{
				mDECREASES(); 

				}
				break;
			case 14 :
				// Pseudo.g:1:95: METHOD
				{
				mMETHOD(); 

				}
				break;
			case 15 :
				// Pseudo.g:1:102: ELSE
				{
				mELSE(); 

				}
				break;
			case 16 :
				// Pseudo.g:1:107: IF
				{
				mIF(); 

				}
				break;
			case 17 :
				// Pseudo.g:1:110: THEN
				{
				mTHEN(); 

				}
				break;
			case 18 :
				// Pseudo.g:1:115: WHILE
				{
				mWHILE(); 

				}
				break;
			case 19 :
				// Pseudo.g:1:121: VAR
				{
				mVAR(); 

				}
				break;
			case 20 :
				// Pseudo.g:1:125: CALL
				{
				mCALL(); 

				}
				break;
			case 21 :
				// Pseudo.g:1:130: INVARIANT
				{
				mINVARIANT(); 

				}
				break;
			case 22 :
				// Pseudo.g:1:140: ASSERT
				{
				mASSERT(); 

				}
				break;
			case 23 :
				// Pseudo.g:1:147: LENGTH
				{
				mLENGTH(); 

				}
				break;
			case 24 :
				// Pseudo.g:1:154: ALL
				{
				mALL(); 

				}
				break;
			case 25 :
				// Pseudo.g:1:158: EX
				{
				mEX(); 

				}
				break;
			case 26 :
				// Pseudo.g:1:161: DOUBLECOLON
				{
				mDOUBLECOLON(); 

				}
				break;
			case 27 :
				// Pseudo.g:1:173: ASSIGN
				{
				mASSIGN(); 

				}
				break;
			case 28 :
				// Pseudo.g:1:180: OR
				{
				mOR(); 

				}
				break;
			case 29 :
				// Pseudo.g:1:183: AND
				{
				mAND(); 

				}
				break;
			case 30 :
				// Pseudo.g:1:187: IMPLIES
				{
				mIMPLIES(); 

				}
				break;
			case 31 :
				// Pseudo.g:1:195: PLUS
				{
				mPLUS(); 

				}
				break;
			case 32 :
				// Pseudo.g:1:200: MINUS
				{
				mMINUS(); 

				}
				break;
			case 33 :
				// Pseudo.g:1:206: NOT
				{
				mNOT(); 

				}
				break;
			case 34 :
				// Pseudo.g:1:210: TIMES
				{
				mTIMES(); 

				}
				break;
			case 35 :
				// Pseudo.g:1:216: UNION
				{
				mUNION(); 

				}
				break;
			case 36 :
				// Pseudo.g:1:222: INTERSECT
				{
				mINTERSECT(); 

				}
				break;
			case 37 :
				// Pseudo.g:1:232: LT
				{
				mLT(); 

				}
				break;
			case 38 :
				// Pseudo.g:1:235: LE
				{
				mLE(); 

				}
				break;
			case 39 :
				// Pseudo.g:1:238: GT
				{
				mGT(); 

				}
				break;
			case 40 :
				// Pseudo.g:1:241: GE
				{
				mGE(); 

				}
				break;
			case 41 :
				// Pseudo.g:1:244: EQ
				{
				mEQ(); 

				}
				break;
			case 42 :
				// Pseudo.g:1:247: DOT
				{
				mDOT(); 

				}
				break;
			case 43 :
				// Pseudo.g:1:251: BLOCK_BEGIN
				{
				mBLOCK_BEGIN(); 

				}
				break;
			case 44 :
				// Pseudo.g:1:263: BLOCK_END
				{
				mBLOCK_END(); 

				}
				break;
			case 45 :
				// Pseudo.g:1:273: ARRAY
				{
				mARRAY(); 

				}
				break;
			case 46 :
				// Pseudo.g:1:279: ID
				{
				mID(); 

				}
				break;
			case 47 :
				// Pseudo.g:1:282: LIT
				{
				mLIT(); 

				}
				break;
			case 48 :
				// Pseudo.g:1:286: WS
				{
				mWS(); 

				}
				break;

		}
	}


	protected DFA5 dfa5 = new DFA5(this);
	static final String DFA5_eotS =
		"\4\uffff\1\46\3\uffff\15\41\3\uffff\1\72\2\uffff\1\74\1\76\1\100\11\uffff"+
		"\1\41\1\103\17\41\1\125\10\uffff\1\126\1\41\1\uffff\1\130\11\41\1\142"+
		"\5\41\3\uffff\1\41\1\uffff\3\41\1\154\3\41\1\160\1\41\1\uffff\1\162\10"+
		"\41\1\uffff\3\41\1\uffff\1\176\1\uffff\1\41\1\u0080\6\41\1\u0087\1\41"+
		"\1\u0089\1\uffff\1\u008a\1\uffff\1\u008b\1\u008c\1\41\1\u008e\1\41\1\u0090"+
		"\1\uffff\1\41\4\uffff\1\41\1\uffff\1\u0093\1\uffff\1\41\1\u0095\1\uffff"+
		"\1\u0096\2\uffff";
	static final String DFA5_eofS =
		"\u0097\uffff";
	static final String DFA5_minS =
		"\1\12\3\uffff\1\72\3\uffff\1\146\2\145\1\154\2\145\2\150\2\141\1\162\1"+
		"\145\1\157\2\uffff\1\75\1\53\2\uffff\1\52\2\75\11\uffff\1\164\1\101\1"+
		"\164\1\161\2\163\1\151\1\143\1\164\1\145\1\151\1\162\1\154\1\163\1\162"+
		"\1\156\1\162\1\76\10\uffff\1\101\1\141\1\uffff\1\101\3\165\1\145\1\163"+
		"\1\162\1\150\1\156\1\154\1\101\1\154\1\145\1\141\1\147\1\141\3\uffff\1"+
		"\162\1\uffff\1\162\1\151\1\162\1\101\1\164\1\145\1\157\1\101\1\145\1\uffff"+
		"\1\101\1\162\1\171\1\164\1\154\1\151\1\156\1\162\1\145\1\uffff\1\163\1"+
		"\141\1\144\1\uffff\1\101\1\uffff\1\164\1\101\1\150\1\154\1\141\1\163\1"+
		"\145\1\163\1\101\1\163\1\101\1\uffff\1\101\1\uffff\2\101\1\156\1\101\1"+
		"\163\1\101\1\uffff\1\145\4\uffff\1\164\1\uffff\1\101\1\uffff\1\163\1\101"+
		"\1\uffff\1\101\2\uffff";
	static final String DFA5_maxS =
		"\1\175\3\uffff\1\75\3\uffff\1\156\2\145\1\170\2\145\2\150\2\141\1\163"+
		"\1\145\1\157\2\uffff\1\75\1\53\2\uffff\1\52\2\75\11\uffff\1\166\1\172"+
		"\2\164\2\163\1\151\1\143\1\164\1\145\1\151\1\162\1\154\1\163\1\162\1\156"+
		"\1\162\1\76\10\uffff\1\172\1\141\1\uffff\1\172\3\165\1\145\1\163\1\162"+
		"\1\150\1\156\1\154\1\172\1\154\1\145\1\141\1\147\1\141\3\uffff\1\162\1"+
		"\uffff\1\162\1\151\1\162\1\172\1\164\1\145\1\157\1\172\1\145\1\uffff\1"+
		"\172\1\162\1\171\1\164\1\154\1\151\1\156\1\162\1\145\1\uffff\1\163\1\141"+
		"\1\144\1\uffff\1\172\1\uffff\1\164\1\172\1\150\1\154\1\141\1\163\1\145"+
		"\1\163\1\172\1\163\1\172\1\uffff\1\172\1\uffff\2\172\1\156\1\172\1\163"+
		"\1\172\1\uffff\1\145\4\uffff\1\164\1\uffff\1\172\1\uffff\1\163\1\172\1"+
		"\uffff\1\172\2\uffff";
	static final String DFA5_acceptS =
		"\1\uffff\1\1\1\2\1\3\1\uffff\1\5\1\6\1\7\15\uffff\1\34\1\35\2\uffff\1"+
		"\40\1\41\3\uffff\1\52\1\53\1\54\1\56\1\57\1\60\1\32\1\33\1\4\22\uffff"+
		"\1\43\1\37\1\44\1\42\1\46\1\45\1\50\1\47\2\uffff\1\20\20\uffff\1\36\1"+
		"\51\1\10\1\uffff\1\11\11\uffff\1\23\11\uffff\1\17\3\uffff\1\21\1\uffff"+
		"\1\24\13\uffff\1\22\1\uffff\1\55\6\uffff\1\31\1\uffff\1\16\1\26\1\27\1"+
		"\30\1\uffff\1\12\1\uffff\1\13\2\uffff\1\14\1\uffff\1\25\1\15";
	static final String DFA5_specialS =
		"\u0097\uffff}>";
	static final String[] DFA5_transitionS = {
			"\1\43\2\uffff\1\43\22\uffff\1\43\1\32\4\uffff\1\26\1\uffff\1\1\1\2\1"+
			"\33\1\30\1\3\1\31\1\36\1\uffff\12\42\1\4\1\5\1\34\1\27\1\35\2\uffff\32"+
			"\41\1\6\1\uffff\1\7\1\uffff\1\41\1\uffff\1\22\1\41\1\21\1\14\1\13\1\24"+
			"\2\41\1\10\2\41\1\23\1\15\4\41\1\12\1\11\1\16\1\41\1\20\1\17\3\41\1\37"+
			"\1\25\1\40",
			"",
			"",
			"",
			"\1\44\2\uffff\1\45",
			"",
			"",
			"",
			"\1\50\7\uffff\1\47",
			"\1\51",
			"\1\52",
			"\1\54\1\uffff\1\53\11\uffff\1\55",
			"\1\56",
			"\1\57",
			"\1\60",
			"\1\61",
			"\1\62",
			"\1\63",
			"\1\65\1\64",
			"\1\66",
			"\1\67",
			"",
			"",
			"\1\70",
			"\1\71",
			"",
			"",
			"\1\73",
			"\1\75",
			"\1\77",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"\1\101\1\uffff\1\102",
			"\32\41\4\uffff\1\41\1\uffff\32\41",
			"\1\104",
			"\1\106\2\uffff\1\105",
			"\1\107",
			"\1\110",
			"\1\111",
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
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"\32\41\4\uffff\1\41\1\uffff\32\41",
			"\1\127",
			"",
			"\32\41\4\uffff\1\41\1\uffff\32\41",
			"\1\131",
			"\1\132",
			"\1\133",
			"\1\134",
			"\1\135",
			"\1\136",
			"\1\137",
			"\1\140",
			"\1\141",
			"\32\41\4\uffff\1\41\1\uffff\32\41",
			"\1\143",
			"\1\144",
			"\1\145",
			"\1\146",
			"\1\147",
			"",
			"",
			"",
			"\1\150",
			"",
			"\1\151",
			"\1\152",
			"\1\153",
			"\32\41\4\uffff\1\41\1\uffff\32\41",
			"\1\155",
			"\1\156",
			"\1\157",
			"\32\41\4\uffff\1\41\1\uffff\32\41",
			"\1\161",
			"",
			"\32\41\4\uffff\1\41\1\uffff\32\41",
			"\1\163",
			"\1\164",
			"\1\165",
			"\1\166",
			"\1\167",
			"\1\170",
			"\1\171",
			"\1\172",
			"",
			"\1\173",
			"\1\174",
			"\1\175",
			"",
			"\32\41\4\uffff\1\41\1\uffff\32\41",
			"",
			"\1\177",
			"\32\41\4\uffff\1\41\1\uffff\32\41",
			"\1\u0081",
			"\1\u0082",
			"\1\u0083",
			"\1\u0084",
			"\1\u0085",
			"\1\u0086",
			"\32\41\4\uffff\1\41\1\uffff\32\41",
			"\1\u0088",
			"\32\41\4\uffff\1\41\1\uffff\32\41",
			"",
			"\32\41\4\uffff\1\41\1\uffff\32\41",
			"",
			"\32\41\4\uffff\1\41\1\uffff\32\41",
			"\32\41\4\uffff\1\41\1\uffff\32\41",
			"\1\u008d",
			"\32\41\4\uffff\1\41\1\uffff\32\41",
			"\1\u008f",
			"\32\41\4\uffff\1\41\1\uffff\32\41",
			"",
			"\1\u0091",
			"",
			"",
			"",
			"",
			"\1\u0092",
			"",
			"\32\41\4\uffff\1\41\1\uffff\32\41",
			"",
			"\1\u0094",
			"\32\41\4\uffff\1\41\1\uffff\32\41",
			"",
			"\32\41\4\uffff\1\41\1\uffff\32\41",
			"",
			""
	};

	static final short[] DFA5_eot = DFA.unpackEncodedString(DFA5_eotS);
	static final short[] DFA5_eof = DFA.unpackEncodedString(DFA5_eofS);
	static final char[] DFA5_min = DFA.unpackEncodedStringToUnsignedChars(DFA5_minS);
	static final char[] DFA5_max = DFA.unpackEncodedStringToUnsignedChars(DFA5_maxS);
	static final short[] DFA5_accept = DFA.unpackEncodedString(DFA5_acceptS);
	static final short[] DFA5_special = DFA.unpackEncodedString(DFA5_specialS);
	static final short[][] DFA5_transition;

	static {
		int numStates = DFA5_transitionS.length;
		DFA5_transition = new short[numStates][];
		for (int i=0; i<numStates; i++) {
			DFA5_transition[i] = DFA.unpackEncodedString(DFA5_transitionS[i]);
		}
	}

	protected class DFA5 extends DFA {

		public DFA5(BaseRecognizer recognizer) {
			this.recognizer = recognizer;
			this.decisionNumber = 5;
			this.eot = DFA5_eot;
			this.eof = DFA5_eof;
			this.min = DFA5_min;
			this.max = DFA5_max;
			this.accept = DFA5_accept;
			this.special = DFA5_special;
			this.transition = DFA5_transition;
		}
		@Override
		public String getDescription() {
			return "1:1: Tokens : ( T__51 | T__52 | T__53 | T__54 | T__55 | T__56 | T__57 | INT | SET | RETURNS | ENSURES | REQUIRES | DECREASES | METHOD | ELSE | IF | THEN | WHILE | VAR | CALL | INVARIANT | ASSERT | LENGTH | ALL | EX | DOUBLECOLON | ASSIGN | OR | AND | IMPLIES | PLUS | MINUS | NOT | TIMES | UNION | INTERSECT | LT | LE | GT | GE | EQ | DOT | BLOCK_BEGIN | BLOCK_END | ARRAY | ID | LIT | WS );";
		}
	}

}
