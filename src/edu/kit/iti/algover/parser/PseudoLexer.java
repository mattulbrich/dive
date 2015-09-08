// $ANTLR 3.5.1 Pseudo.g 2015-08-14 16:04:44

  package edu.kit.iti.algover.parser;


import org.antlr.runtime.*;
import java.util.Stack;
import java.util.List;
import java.util.ArrayList;

@SuppressWarnings("all")
public class PseudoLexer extends Lexer {
	public static final int EOF=-1;
	public static final int T__46=46;
	public static final int T__47=47;
	public static final int T__48=48;
	public static final int T__49=49;
	public static final int T__50=50;
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
	public static final int CALL=12;
	public static final int DECREASES=13;
	public static final int ELSE=14;
	public static final int ENSURES=15;
	public static final int EQ=16;
	public static final int EX=17;
	public static final int FUNCTION=18;
	public static final int GE=19;
	public static final int GT=20;
	public static final int ID=21;
	public static final int IF=22;
	public static final int IMPLIES=23;
	public static final int INT=24;
	public static final int INTERSECT=25;
	public static final int INVARIANT=26;
	public static final int LE=27;
	public static final int LISTEX=28;
	public static final int LIT=29;
	public static final int LT=30;
	public static final int MINUS=31;
	public static final int NOT=32;
	public static final int OR=33;
	public static final int PLUS=34;
	public static final int REQUIRES=35;
	public static final int RESULTS=36;
	public static final int RETURNS=37;
	public static final int SET=38;
	public static final int SETEX=39;
	public static final int THEN=40;
	public static final int TIMES=41;
	public static final int UNION=42;
	public static final int VAR=43;
	public static final int WHILE=44;
	public static final int WS=45;

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

	// $ANTLR start "T__46"
	public final void mT__46() throws RecognitionException {
		try {
			int _type = T__46;
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
	// $ANTLR end "T__46"

	// $ANTLR start "T__47"
	public final void mT__47() throws RecognitionException {
		try {
			int _type = T__47;
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
	// $ANTLR end "T__47"

	// $ANTLR start "T__48"
	public final void mT__48() throws RecognitionException {
		try {
			int _type = T__48;
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
	// $ANTLR end "T__48"

	// $ANTLR start "T__49"
	public final void mT__49() throws RecognitionException {
		try {
			int _type = T__49;
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
	// $ANTLR end "T__49"

	// $ANTLR start "T__50"
	public final void mT__50() throws RecognitionException {
		try {
			int _type = T__50;
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
	// $ANTLR end "T__50"

	// $ANTLR start "T__51"
	public final void mT__51() throws RecognitionException {
		try {
			int _type = T__51;
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
	// $ANTLR end "T__51"

	// $ANTLR start "T__52"
	public final void mT__52() throws RecognitionException {
		try {
			int _type = T__52;
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
	// $ANTLR end "T__52"

	// $ANTLR start "T__53"
	public final void mT__53() throws RecognitionException {
		try {
			int _type = T__53;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// Pseudo.g:13:7: ( 'begin' )
			// Pseudo.g:13:9: 'begin'
			{
			match("begin"); 

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
			// Pseudo.g:14:7: ( 'do' )
			// Pseudo.g:14:9: 'do'
			{
			match("do"); 

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
			// Pseudo.g:15:7: ( 'end' )
			// Pseudo.g:15:9: 'end'
			{
			match("end"); 

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
			// Pseudo.g:16:7: ( '{' )
			// Pseudo.g:16:9: '{'
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
	// $ANTLR end "T__56"

	// $ANTLR start "T__57"
	public final void mT__57() throws RecognitionException {
		try {
			int _type = T__57;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// Pseudo.g:17:7: ( '}' )
			// Pseudo.g:17:9: '}'
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
	// $ANTLR end "T__57"

	// $ANTLR start "INT"
	public final void mINT() throws RecognitionException {
		try {
			int _type = INT;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// Pseudo.g:25:5: ( 'int' )
			// Pseudo.g:25:7: 'int'
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
			// Pseudo.g:26:5: ( 'set' )
			// Pseudo.g:26:7: 'set'
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

	// $ANTLR start "ARRAY"
	public final void mARRAY() throws RecognitionException {
		try {
			int _type = ARRAY;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// Pseudo.g:27:7: ( 'array' )
			// Pseudo.g:27:9: 'array'
			{
			match("array"); 

			}

			state.type = _type;
			state.channel = _channel;
		}
		finally {
			// do for sure before leaving
		}
	}
	// $ANTLR end "ARRAY"

	// $ANTLR start "RETURNS"
	public final void mRETURNS() throws RecognitionException {
		try {
			int _type = RETURNS;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// Pseudo.g:28:9: ( 'returns' )
			// Pseudo.g:28:11: 'returns'
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
			// Pseudo.g:29:8: ( 'ensures' )
			// Pseudo.g:29:10: 'ensures'
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
			// Pseudo.g:30:9: ( 'requires' )
			// Pseudo.g:30:11: 'requires'
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
			// Pseudo.g:31:10: ( 'decreases' )
			// Pseudo.g:31:12: 'decreases'
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
			// Pseudo.g:32:9: ( 'function' )
			// Pseudo.g:32:11: 'function'
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

	// $ANTLR start "ELSE"
	public final void mELSE() throws RecognitionException {
		try {
			int _type = ELSE;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// Pseudo.g:33:5: ( 'else' )
			// Pseudo.g:33:7: 'else'
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
			// Pseudo.g:34:3: ( 'if' )
			// Pseudo.g:34:5: 'if'
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
			// Pseudo.g:35:5: ( 'then' )
			// Pseudo.g:35:7: 'then'
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
			// Pseudo.g:36:6: ( 'while' )
			// Pseudo.g:36:8: 'while'
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
			// Pseudo.g:37:4: ( 'var' )
			// Pseudo.g:37:6: 'var'
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

	// $ANTLR start "NOT"
	public final void mNOT() throws RecognitionException {
		try {
			int _type = NOT;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// Pseudo.g:38:4: ( 'not' )
			// Pseudo.g:38:6: 'not'
			{
			match("not"); 

			}

			state.type = _type;
			state.channel = _channel;
		}
		finally {
			// do for sure before leaving
		}
	}
	// $ANTLR end "NOT"

	// $ANTLR start "CALL"
	public final void mCALL() throws RecognitionException {
		try {
			int _type = CALL;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// Pseudo.g:39:5: ( 'call' )
			// Pseudo.g:39:6: 'call'
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
			// Pseudo.g:40:10: ( 'invariant' )
			// Pseudo.g:40:12: 'invariant'
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
			// Pseudo.g:41:7: ( 'assert' )
			// Pseudo.g:41:9: 'assert'
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
			// Pseudo.g:43:4: ( '\\\\all' )
			// Pseudo.g:43:6: '\\\\all'
			{
			match("\\all"); 

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
			// Pseudo.g:44:3: ( '\\\\ex' )
			// Pseudo.g:44:5: '\\\\ex'
			{
			match("\\ex"); 

			}

			state.type = _type;
			state.channel = _channel;
		}
		finally {
			// do for sure before leaving
		}
	}
	// $ANTLR end "EX"

	// $ANTLR start "ASSIGN"
	public final void mASSIGN() throws RecognitionException {
		try {
			int _type = ASSIGN;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// Pseudo.g:46:7: ( ':=' )
			// Pseudo.g:46:9: ':='
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
			// Pseudo.g:47:3: ( '||' )
			// Pseudo.g:47:5: '||'
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
			// Pseudo.g:48:4: ( '&&' )
			// Pseudo.g:48:6: '&&'
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
			// Pseudo.g:49:8: ( '==>' )
			// Pseudo.g:49:10: '==>'
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
			// Pseudo.g:50:5: ( '+' )
			// Pseudo.g:50:7: '+'
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
			// Pseudo.g:51:6: ( '-' )
			// Pseudo.g:51:8: '-'
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

	// $ANTLR start "TIMES"
	public final void mTIMES() throws RecognitionException {
		try {
			int _type = TIMES;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// Pseudo.g:52:6: ( '*' )
			// Pseudo.g:52:8: '*'
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
			// Pseudo.g:53:6: ( '++' )
			// Pseudo.g:53:8: '++'
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
			// Pseudo.g:54:10: ( '**' )
			// Pseudo.g:54:12: '**'
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
			// Pseudo.g:55:3: ( '<' )
			// Pseudo.g:55:5: '<'
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
			// Pseudo.g:56:3: ( '<=' )
			// Pseudo.g:56:5: '<='
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
			// Pseudo.g:57:3: ( '>' )
			// Pseudo.g:57:5: '>'
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
			// Pseudo.g:58:3: ( '>=' )
			// Pseudo.g:58:5: '>='
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
			// Pseudo.g:59:3: ( '=' )
			// Pseudo.g:59:5: '='
			{
			match('='); 
			}

			state.type = _type;
			state.channel = _channel;
		}
		finally {
			// do for sure before leaving
		}
	}
	// $ANTLR end "EQ"

	// $ANTLR start "ID"
	public final void mID() throws RecognitionException {
		try {
			int _type = ID;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// Pseudo.g:61:4: ( ( 'a' .. 'z' )+ )
			// Pseudo.g:61:6: ( 'a' .. 'z' )+
			{
			// Pseudo.g:61:6: ( 'a' .. 'z' )+
			int cnt1=0;
			loop1:
			while (true) {
				int alt1=2;
				int LA1_0 = input.LA(1);
				if ( ((LA1_0 >= 'a' && LA1_0 <= 'z')) ) {
					alt1=1;
				}

				switch (alt1) {
				case 1 :
					// Pseudo.g:
					{
					if ( (input.LA(1) >= 'a' && input.LA(1) <= 'z') ) {
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
					if ( cnt1 >= 1 ) break loop1;
					EarlyExitException eee = new EarlyExitException(1, input);
					throw eee;
				}
				cnt1++;
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
			// Pseudo.g:62:5: ( ( '0' .. '9' )+ )
			// Pseudo.g:62:7: ( '0' .. '9' )+
			{
			// Pseudo.g:62:7: ( '0' .. '9' )+
			int cnt2=0;
			loop2:
			while (true) {
				int alt2=2;
				int LA2_0 = input.LA(1);
				if ( ((LA2_0 >= '0' && LA2_0 <= '9')) ) {
					alt2=1;
				}

				switch (alt2) {
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
					if ( cnt2 >= 1 ) break loop2;
					EarlyExitException eee = new EarlyExitException(2, input);
					throw eee;
				}
				cnt2++;
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
			// Pseudo.g:63:4: ( ( ' ' | '\\n' | '\\r' ) )
			// Pseudo.g:63:6: ( ' ' | '\\n' | '\\r' )
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
		// Pseudo.g:1:8: ( T__46 | T__47 | T__48 | T__49 | T__50 | T__51 | T__52 | T__53 | T__54 | T__55 | T__56 | T__57 | INT | SET | ARRAY | RETURNS | ENSURES | REQUIRES | DECREASES | FUNCTION | ELSE | IF | THEN | WHILE | VAR | NOT | CALL | INVARIANT | ASSERT | ALL | EX | ASSIGN | OR | AND | IMPLIES | PLUS | MINUS | TIMES | UNION | INTERSECT | LT | LE | GT | GE | EQ | ID | LIT | WS )
		int alt3=48;
		alt3 = dfa3.predict(input);
		switch (alt3) {
			case 1 :
				// Pseudo.g:1:10: T__46
				{
				mT__46(); 

				}
				break;
			case 2 :
				// Pseudo.g:1:16: T__47
				{
				mT__47(); 

				}
				break;
			case 3 :
				// Pseudo.g:1:22: T__48
				{
				mT__48(); 

				}
				break;
			case 4 :
				// Pseudo.g:1:28: T__49
				{
				mT__49(); 

				}
				break;
			case 5 :
				// Pseudo.g:1:34: T__50
				{
				mT__50(); 

				}
				break;
			case 6 :
				// Pseudo.g:1:40: T__51
				{
				mT__51(); 

				}
				break;
			case 7 :
				// Pseudo.g:1:46: T__52
				{
				mT__52(); 

				}
				break;
			case 8 :
				// Pseudo.g:1:52: T__53
				{
				mT__53(); 

				}
				break;
			case 9 :
				// Pseudo.g:1:58: T__54
				{
				mT__54(); 

				}
				break;
			case 10 :
				// Pseudo.g:1:64: T__55
				{
				mT__55(); 

				}
				break;
			case 11 :
				// Pseudo.g:1:70: T__56
				{
				mT__56(); 

				}
				break;
			case 12 :
				// Pseudo.g:1:76: T__57
				{
				mT__57(); 

				}
				break;
			case 13 :
				// Pseudo.g:1:82: INT
				{
				mINT(); 

				}
				break;
			case 14 :
				// Pseudo.g:1:86: SET
				{
				mSET(); 

				}
				break;
			case 15 :
				// Pseudo.g:1:90: ARRAY
				{
				mARRAY(); 

				}
				break;
			case 16 :
				// Pseudo.g:1:96: RETURNS
				{
				mRETURNS(); 

				}
				break;
			case 17 :
				// Pseudo.g:1:104: ENSURES
				{
				mENSURES(); 

				}
				break;
			case 18 :
				// Pseudo.g:1:112: REQUIRES
				{
				mREQUIRES(); 

				}
				break;
			case 19 :
				// Pseudo.g:1:121: DECREASES
				{
				mDECREASES(); 

				}
				break;
			case 20 :
				// Pseudo.g:1:131: FUNCTION
				{
				mFUNCTION(); 

				}
				break;
			case 21 :
				// Pseudo.g:1:140: ELSE
				{
				mELSE(); 

				}
				break;
			case 22 :
				// Pseudo.g:1:145: IF
				{
				mIF(); 

				}
				break;
			case 23 :
				// Pseudo.g:1:148: THEN
				{
				mTHEN(); 

				}
				break;
			case 24 :
				// Pseudo.g:1:153: WHILE
				{
				mWHILE(); 

				}
				break;
			case 25 :
				// Pseudo.g:1:159: VAR
				{
				mVAR(); 

				}
				break;
			case 26 :
				// Pseudo.g:1:163: NOT
				{
				mNOT(); 

				}
				break;
			case 27 :
				// Pseudo.g:1:167: CALL
				{
				mCALL(); 

				}
				break;
			case 28 :
				// Pseudo.g:1:172: INVARIANT
				{
				mINVARIANT(); 

				}
				break;
			case 29 :
				// Pseudo.g:1:182: ASSERT
				{
				mASSERT(); 

				}
				break;
			case 30 :
				// Pseudo.g:1:189: ALL
				{
				mALL(); 

				}
				break;
			case 31 :
				// Pseudo.g:1:193: EX
				{
				mEX(); 

				}
				break;
			case 32 :
				// Pseudo.g:1:196: ASSIGN
				{
				mASSIGN(); 

				}
				break;
			case 33 :
				// Pseudo.g:1:203: OR
				{
				mOR(); 

				}
				break;
			case 34 :
				// Pseudo.g:1:206: AND
				{
				mAND(); 

				}
				break;
			case 35 :
				// Pseudo.g:1:210: IMPLIES
				{
				mIMPLIES(); 

				}
				break;
			case 36 :
				// Pseudo.g:1:218: PLUS
				{
				mPLUS(); 

				}
				break;
			case 37 :
				// Pseudo.g:1:223: MINUS
				{
				mMINUS(); 

				}
				break;
			case 38 :
				// Pseudo.g:1:229: TIMES
				{
				mTIMES(); 

				}
				break;
			case 39 :
				// Pseudo.g:1:235: UNION
				{
				mUNION(); 

				}
				break;
			case 40 :
				// Pseudo.g:1:241: INTERSECT
				{
				mINTERSECT(); 

				}
				break;
			case 41 :
				// Pseudo.g:1:251: LT
				{
				mLT(); 

				}
				break;
			case 42 :
				// Pseudo.g:1:254: LE
				{
				mLE(); 

				}
				break;
			case 43 :
				// Pseudo.g:1:257: GT
				{
				mGT(); 

				}
				break;
			case 44 :
				// Pseudo.g:1:260: GE
				{
				mGE(); 

				}
				break;
			case 45 :
				// Pseudo.g:1:263: EQ
				{
				mEQ(); 

				}
				break;
			case 46 :
				// Pseudo.g:1:266: ID
				{
				mID(); 

				}
				break;
			case 47 :
				// Pseudo.g:1:269: LIT
				{
				mLIT(); 

				}
				break;
			case 48 :
				// Pseudo.g:1:273: WS
				{
				mWS(); 

				}
				break;

		}
	}


	protected DFA3 dfa3 = new DFA3(this);
	static final String DFA3_eotS =
		"\4\uffff\1\44\3\uffff\3\40\2\uffff\12\40\3\uffff\1\71\1\73\1\uffff\1\75"+
		"\1\77\1\101\5\uffff\1\40\1\103\4\40\1\112\12\40\14\uffff\1\40\1\uffff"+
		"\1\40\1\130\2\40\1\133\1\40\1\uffff\1\135\7\40\1\145\1\146\3\40\1\uffff"+
		"\1\40\1\153\1\uffff\1\40\1\uffff\5\40\1\162\1\40\2\uffff\1\164\1\165\2"+
		"\40\1\uffff\1\40\1\171\4\40\1\uffff\1\176\2\uffff\3\40\1\uffff\1\u0082"+
		"\3\40\1\uffff\1\40\1\u0087\1\40\1\uffff\1\u0089\3\40\1\uffff\1\40\1\uffff"+
		"\1\u008e\1\u008f\1\u0090\1\u0091\4\uffff";
	static final String DFA3_eofS =
		"\u0092\uffff";
	static final String DFA3_minS =
		"\1\12\3\uffff\1\75\3\uffff\2\145\1\154\2\uffff\1\146\1\145\1\162\1\145"+
		"\1\165\2\150\1\141\1\157\2\141\2\uffff\1\75\1\53\1\uffff\1\52\2\75\5\uffff"+
		"\1\147\1\141\1\143\1\144\1\163\1\164\1\141\1\164\1\162\1\163\1\161\1\156"+
		"\1\145\1\151\1\162\1\164\1\154\14\uffff\1\151\1\uffff\1\162\1\141\1\165"+
		"\1\145\2\141\1\uffff\2\141\1\145\2\165\1\143\1\156\1\154\2\141\1\154\1"+
		"\156\1\145\1\uffff\1\162\1\141\1\uffff\1\162\1\uffff\1\171\2\162\1\151"+
		"\1\164\1\141\1\145\2\uffff\3\141\1\145\1\uffff\1\151\1\141\1\164\1\156"+
		"\1\162\1\151\1\uffff\1\141\2\uffff\2\163\1\141\1\uffff\1\141\1\163\1\145"+
		"\1\157\1\uffff\1\145\1\141\1\156\1\uffff\1\141\1\163\1\156\1\163\1\uffff"+
		"\1\164\1\uffff\4\141\4\uffff";
	static final String DFA3_maxS =
		"\1\175\3\uffff\1\75\3\uffff\1\145\1\157\1\156\2\uffff\1\156\1\145\1\163"+
		"\1\145\1\165\2\150\1\141\1\157\1\141\1\145\2\uffff\1\75\1\53\1\uffff\1"+
		"\52\2\75\5\uffff\1\147\1\172\1\143\2\163\1\166\1\172\1\164\1\162\1\163"+
		"\1\164\1\156\1\145\1\151\1\162\1\164\1\154\14\uffff\1\151\1\uffff\1\162"+
		"\1\172\1\165\1\145\1\172\1\141\1\uffff\1\172\1\141\1\145\2\165\1\143\1"+
		"\156\1\154\2\172\1\154\1\156\1\145\1\uffff\1\162\1\172\1\uffff\1\162\1"+
		"\uffff\1\171\2\162\1\151\1\164\1\172\1\145\2\uffff\2\172\1\141\1\145\1"+
		"\uffff\1\151\1\172\1\164\1\156\1\162\1\151\1\uffff\1\172\2\uffff\2\163"+
		"\1\141\1\uffff\1\172\1\163\1\145\1\157\1\uffff\1\145\1\172\1\156\1\uffff"+
		"\1\172\1\163\1\156\1\163\1\uffff\1\164\1\uffff\4\172\4\uffff";
	static final String DFA3_acceptS =
		"\1\uffff\1\1\1\2\1\3\1\uffff\1\5\1\6\1\7\3\uffff\1\13\1\14\13\uffff\1"+
		"\41\1\42\2\uffff\1\45\3\uffff\1\56\1\57\1\60\1\40\1\4\21\uffff\1\36\1"+
		"\37\1\43\1\55\1\47\1\44\1\50\1\46\1\52\1\51\1\54\1\53\1\uffff\1\11\6\uffff"+
		"\1\26\15\uffff\1\12\2\uffff\1\15\1\uffff\1\16\7\uffff\1\31\1\32\4\uffff"+
		"\1\25\6\uffff\1\27\1\uffff\1\33\1\10\3\uffff\1\17\4\uffff\1\30\3\uffff"+
		"\1\35\4\uffff\1\21\1\uffff\1\20\4\uffff\1\22\1\24\1\23\1\34";
	static final String DFA3_specialS =
		"\u0092\uffff}>";
	static final String[] DFA3_transitionS = {
			"\1\42\2\uffff\1\42\22\uffff\1\42\5\uffff\1\31\1\uffff\1\1\1\2\1\35\1"+
			"\33\1\3\1\34\2\uffff\12\41\1\4\1\5\1\36\1\32\1\37\34\uffff\1\6\1\27\1"+
			"\7\3\uffff\1\17\1\10\1\26\1\11\1\12\1\21\2\40\1\15\4\40\1\25\3\40\1\20"+
			"\1\16\1\22\1\40\1\24\1\23\3\40\1\13\1\30\1\14",
			"",
			"",
			"",
			"\1\43",
			"",
			"",
			"",
			"\1\45",
			"\1\47\11\uffff\1\46",
			"\1\51\1\uffff\1\50",
			"",
			"",
			"\1\53\7\uffff\1\52",
			"\1\54",
			"\1\55\1\56",
			"\1\57",
			"\1\60",
			"\1\61",
			"\1\62",
			"\1\63",
			"\1\64",
			"\1\65",
			"\1\66\3\uffff\1\67",
			"",
			"",
			"\1\70",
			"\1\72",
			"",
			"\1\74",
			"\1\76",
			"\1\100",
			"",
			"",
			"",
			"",
			"",
			"\1\102",
			"\32\40",
			"\1\104",
			"\1\105\16\uffff\1\106",
			"\1\107",
			"\1\110\1\uffff\1\111",
			"\32\40",
			"\1\113",
			"\1\114",
			"\1\115",
			"\1\117\2\uffff\1\116",
			"\1\120",
			"\1\121",
			"\1\122",
			"\1\123",
			"\1\124",
			"\1\125",
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
			"",
			"",
			"\1\126",
			"",
			"\1\127",
			"\32\40",
			"\1\131",
			"\1\132",
			"\32\40",
			"\1\134",
			"",
			"\32\40",
			"\1\136",
			"\1\137",
			"\1\140",
			"\1\141",
			"\1\142",
			"\1\143",
			"\1\144",
			"\32\40",
			"\32\40",
			"\1\147",
			"\1\150",
			"\1\151",
			"",
			"\1\152",
			"\32\40",
			"",
			"\1\154",
			"",
			"\1\155",
			"\1\156",
			"\1\157",
			"\1\160",
			"\1\161",
			"\32\40",
			"\1\163",
			"",
			"",
			"\32\40",
			"\32\40",
			"\1\166",
			"\1\167",
			"",
			"\1\170",
			"\32\40",
			"\1\172",
			"\1\173",
			"\1\174",
			"\1\175",
			"",
			"\32\40",
			"",
			"",
			"\1\177",
			"\1\u0080",
			"\1\u0081",
			"",
			"\32\40",
			"\1\u0083",
			"\1\u0084",
			"\1\u0085",
			"",
			"\1\u0086",
			"\32\40",
			"\1\u0088",
			"",
			"\32\40",
			"\1\u008a",
			"\1\u008b",
			"\1\u008c",
			"",
			"\1\u008d",
			"",
			"\32\40",
			"\32\40",
			"\32\40",
			"\32\40",
			"",
			"",
			"",
			""
	};

	static final short[] DFA3_eot = DFA.unpackEncodedString(DFA3_eotS);
	static final short[] DFA3_eof = DFA.unpackEncodedString(DFA3_eofS);
	static final char[] DFA3_min = DFA.unpackEncodedStringToUnsignedChars(DFA3_minS);
	static final char[] DFA3_max = DFA.unpackEncodedStringToUnsignedChars(DFA3_maxS);
	static final short[] DFA3_accept = DFA.unpackEncodedString(DFA3_acceptS);
	static final short[] DFA3_special = DFA.unpackEncodedString(DFA3_specialS);
	static final short[][] DFA3_transition;

	static {
		int numStates = DFA3_transitionS.length;
		DFA3_transition = new short[numStates][];
		for (int i=0; i<numStates; i++) {
			DFA3_transition[i] = DFA.unpackEncodedString(DFA3_transitionS[i]);
		}
	}

	protected class DFA3 extends DFA {

		public DFA3(BaseRecognizer recognizer) {
			this.recognizer = recognizer;
			this.decisionNumber = 3;
			this.eot = DFA3_eot;
			this.eof = DFA3_eof;
			this.min = DFA3_min;
			this.max = DFA3_max;
			this.accept = DFA3_accept;
			this.special = DFA3_special;
			this.transition = DFA3_transition;
		}
		@Override
		public String getDescription() {
			return "1:1: Tokens : ( T__46 | T__47 | T__48 | T__49 | T__50 | T__51 | T__52 | T__53 | T__54 | T__55 | T__56 | T__57 | INT | SET | ARRAY | RETURNS | ENSURES | REQUIRES | DECREASES | FUNCTION | ELSE | IF | THEN | WHILE | VAR | NOT | CALL | INVARIANT | ASSERT | ALL | EX | ASSIGN | OR | AND | IMPLIES | PLUS | MINUS | TIMES | UNION | INTERSECT | LT | LE | GT | GE | EQ | ID | LIT | WS );";
		}
	}

}
