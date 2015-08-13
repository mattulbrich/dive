// $ANTLR 3.5.1 Pseudo.g 2015-08-11 13:28:09

  package edu.kit.iti.algover.parser;


import org.antlr.runtime.*;
import java.util.Stack;
import java.util.List;
import java.util.ArrayList;

@SuppressWarnings("all")
public class PseudoLexer extends Lexer {
	public static final int EOF=-1;
	public static final int T__32=32;
	public static final int T__33=33;
	public static final int T__34=34;
	public static final int T__35=35;
	public static final int T__36=36;
	public static final int T__37=37;
	public static final int T__38=38;
	public static final int T__39=39;
	public static final int T__40=40;
	public static final int T__41=41;
	public static final int T__42=42;
	public static final int T__43=43;
	public static final int T__44=44;
	public static final int T__45=45;
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
	public static final int ALL=4;
	public static final int ARGS=5;
	public static final int ARRAY=6;
	public static final int ARRAY_ACCESS=7;
	public static final int ASSIGN=8;
	public static final int BLOCK=9;
	public static final int CALL=10;
	public static final int DECREASES=11;
	public static final int ELSE=12;
	public static final int ENSURES=13;
	public static final int EX=14;
	public static final int FUNCTION=15;
	public static final int ID=16;
	public static final int IF=17;
	public static final int INT=18;
	public static final int INVARIANT=19;
	public static final int LISTEX=20;
	public static final int LIT=21;
	public static final int NOT=22;
	public static final int REQUIRES=23;
	public static final int RESULTS=24;
	public static final int RETURNS=25;
	public static final int SET=26;
	public static final int SETEX=27;
	public static final int THEN=28;
	public static final int VAR=29;
	public static final int WHILE=30;
	public static final int WS=31;

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

	// $ANTLR start "T__32"
	public final void mT__32() throws RecognitionException {
		try {
			int _type = T__32;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// Pseudo.g:6:7: ( '&&' )
			// Pseudo.g:6:9: '&&'
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
	// $ANTLR end "T__32"

	// $ANTLR start "T__33"
	public final void mT__33() throws RecognitionException {
		try {
			int _type = T__33;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// Pseudo.g:7:7: ( '(' )
			// Pseudo.g:7:9: '('
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
	// $ANTLR end "T__33"

	// $ANTLR start "T__34"
	public final void mT__34() throws RecognitionException {
		try {
			int _type = T__34;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// Pseudo.g:8:7: ( ')' )
			// Pseudo.g:8:9: ')'
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
	// $ANTLR end "T__34"

	// $ANTLR start "T__35"
	public final void mT__35() throws RecognitionException {
		try {
			int _type = T__35;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// Pseudo.g:9:7: ( '*' )
			// Pseudo.g:9:9: '*'
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
	// $ANTLR end "T__35"

	// $ANTLR start "T__36"
	public final void mT__36() throws RecognitionException {
		try {
			int _type = T__36;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// Pseudo.g:10:7: ( '**' )
			// Pseudo.g:10:9: '**'
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
	// $ANTLR end "T__36"

	// $ANTLR start "T__37"
	public final void mT__37() throws RecognitionException {
		try {
			int _type = T__37;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// Pseudo.g:11:7: ( '+' )
			// Pseudo.g:11:9: '+'
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
	// $ANTLR end "T__37"

	// $ANTLR start "T__38"
	public final void mT__38() throws RecognitionException {
		try {
			int _type = T__38;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// Pseudo.g:12:7: ( '++' )
			// Pseudo.g:12:9: '++'
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
	// $ANTLR end "T__38"

	// $ANTLR start "T__39"
	public final void mT__39() throws RecognitionException {
		try {
			int _type = T__39;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// Pseudo.g:13:7: ( ',' )
			// Pseudo.g:13:9: ','
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
	// $ANTLR end "T__39"

	// $ANTLR start "T__40"
	public final void mT__40() throws RecognitionException {
		try {
			int _type = T__40;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// Pseudo.g:14:7: ( '-' )
			// Pseudo.g:14:9: '-'
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
	// $ANTLR end "T__40"

	// $ANTLR start "T__41"
	public final void mT__41() throws RecognitionException {
		try {
			int _type = T__41;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// Pseudo.g:15:7: ( ':' )
			// Pseudo.g:15:9: ':'
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
	// $ANTLR end "T__41"

	// $ANTLR start "T__42"
	public final void mT__42() throws RecognitionException {
		try {
			int _type = T__42;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// Pseudo.g:16:7: ( ';' )
			// Pseudo.g:16:9: ';'
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
	// $ANTLR end "T__42"

	// $ANTLR start "T__43"
	public final void mT__43() throws RecognitionException {
		try {
			int _type = T__43;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// Pseudo.g:17:7: ( '<' )
			// Pseudo.g:17:9: '<'
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
	// $ANTLR end "T__43"

	// $ANTLR start "T__44"
	public final void mT__44() throws RecognitionException {
		try {
			int _type = T__44;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// Pseudo.g:18:7: ( '<=' )
			// Pseudo.g:18:9: '<='
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
	// $ANTLR end "T__44"

	// $ANTLR start "T__45"
	public final void mT__45() throws RecognitionException {
		try {
			int _type = T__45;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// Pseudo.g:19:7: ( '=' )
			// Pseudo.g:19:9: '='
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
	// $ANTLR end "T__45"

	// $ANTLR start "T__46"
	public final void mT__46() throws RecognitionException {
		try {
			int _type = T__46;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// Pseudo.g:20:7: ( '==>' )
			// Pseudo.g:20:9: '==>'
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
	// $ANTLR end "T__46"

	// $ANTLR start "T__47"
	public final void mT__47() throws RecognitionException {
		try {
			int _type = T__47;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// Pseudo.g:21:7: ( '>' )
			// Pseudo.g:21:9: '>'
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
	// $ANTLR end "T__47"

	// $ANTLR start "T__48"
	public final void mT__48() throws RecognitionException {
		try {
			int _type = T__48;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// Pseudo.g:22:7: ( '>=' )
			// Pseudo.g:22:9: '>='
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
	// $ANTLR end "T__48"

	// $ANTLR start "T__49"
	public final void mT__49() throws RecognitionException {
		try {
			int _type = T__49;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// Pseudo.g:23:7: ( '[' )
			// Pseudo.g:23:9: '['
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
	// $ANTLR end "T__49"

	// $ANTLR start "T__50"
	public final void mT__50() throws RecognitionException {
		try {
			int _type = T__50;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// Pseudo.g:24:7: ( ']' )
			// Pseudo.g:24:9: ']'
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
	// $ANTLR end "T__50"

	// $ANTLR start "T__51"
	public final void mT__51() throws RecognitionException {
		try {
			int _type = T__51;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// Pseudo.g:25:7: ( 'begin' )
			// Pseudo.g:25:9: 'begin'
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
	// $ANTLR end "T__51"

	// $ANTLR start "T__52"
	public final void mT__52() throws RecognitionException {
		try {
			int _type = T__52;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// Pseudo.g:26:7: ( 'do' )
			// Pseudo.g:26:9: 'do'
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
	// $ANTLR end "T__52"

	// $ANTLR start "T__53"
	public final void mT__53() throws RecognitionException {
		try {
			int _type = T__53;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// Pseudo.g:27:7: ( 'end' )
			// Pseudo.g:27:9: 'end'
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
	// $ANTLR end "T__53"

	// $ANTLR start "T__54"
	public final void mT__54() throws RecognitionException {
		try {
			int _type = T__54;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// Pseudo.g:28:7: ( '{' )
			// Pseudo.g:28:9: '{'
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
	// $ANTLR end "T__54"

	// $ANTLR start "T__55"
	public final void mT__55() throws RecognitionException {
		try {
			int _type = T__55;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// Pseudo.g:29:7: ( '||' )
			// Pseudo.g:29:9: '||'
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
	// $ANTLR end "T__55"

	// $ANTLR start "T__56"
	public final void mT__56() throws RecognitionException {
		try {
			int _type = T__56;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// Pseudo.g:30:7: ( '}' )
			// Pseudo.g:30:9: '}'
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
	// $ANTLR end "T__56"

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

	// $ANTLR start "ALL"
	public final void mALL() throws RecognitionException {
		try {
			int _type = ALL;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// Pseudo.g:42:4: ( '\\\\all' )
			// Pseudo.g:42:6: '\\\\all'
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
			// Pseudo.g:43:3: ( '\\\\ex' )
			// Pseudo.g:43:5: '\\\\ex'
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
			// Pseudo.g:45:7: ( ':=' )
			// Pseudo.g:45:9: ':='
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

	// $ANTLR start "ID"
	public final void mID() throws RecognitionException {
		try {
			int _type = ID;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// Pseudo.g:47:4: ( ( 'a' .. 'z' )+ )
			// Pseudo.g:47:6: ( 'a' .. 'z' )+
			{
			// Pseudo.g:47:6: ( 'a' .. 'z' )+
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
			// Pseudo.g:48:5: ( ( '0' .. '9' )+ )
			// Pseudo.g:48:7: ( '0' .. '9' )+
			{
			// Pseudo.g:48:7: ( '0' .. '9' )+
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
			// Pseudo.g:49:4: ( ( ' ' | '\\n' | '\\r' ) )
			// Pseudo.g:49:6: ( ' ' | '\\n' | '\\r' )
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
		// Pseudo.g:1:8: ( T__32 | T__33 | T__34 | T__35 | T__36 | T__37 | T__38 | T__39 | T__40 | T__41 | T__42 | T__43 | T__44 | T__45 | T__46 | T__47 | T__48 | T__49 | T__50 | T__51 | T__52 | T__53 | T__54 | T__55 | T__56 | INT | SET | ARRAY | RETURNS | ENSURES | REQUIRES | DECREASES | FUNCTION | ELSE | IF | THEN | WHILE | VAR | NOT | CALL | INVARIANT | ALL | EX | ASSIGN | ID | LIT | WS )
		int alt3=47;
		alt3 = dfa3.predict(input);
		switch (alt3) {
			case 1 :
				// Pseudo.g:1:10: T__32
				{
				mT__32(); 

				}
				break;
			case 2 :
				// Pseudo.g:1:16: T__33
				{
				mT__33(); 

				}
				break;
			case 3 :
				// Pseudo.g:1:22: T__34
				{
				mT__34(); 

				}
				break;
			case 4 :
				// Pseudo.g:1:28: T__35
				{
				mT__35(); 

				}
				break;
			case 5 :
				// Pseudo.g:1:34: T__36
				{
				mT__36(); 

				}
				break;
			case 6 :
				// Pseudo.g:1:40: T__37
				{
				mT__37(); 

				}
				break;
			case 7 :
				// Pseudo.g:1:46: T__38
				{
				mT__38(); 

				}
				break;
			case 8 :
				// Pseudo.g:1:52: T__39
				{
				mT__39(); 

				}
				break;
			case 9 :
				// Pseudo.g:1:58: T__40
				{
				mT__40(); 

				}
				break;
			case 10 :
				// Pseudo.g:1:64: T__41
				{
				mT__41(); 

				}
				break;
			case 11 :
				// Pseudo.g:1:70: T__42
				{
				mT__42(); 

				}
				break;
			case 12 :
				// Pseudo.g:1:76: T__43
				{
				mT__43(); 

				}
				break;
			case 13 :
				// Pseudo.g:1:82: T__44
				{
				mT__44(); 

				}
				break;
			case 14 :
				// Pseudo.g:1:88: T__45
				{
				mT__45(); 

				}
				break;
			case 15 :
				// Pseudo.g:1:94: T__46
				{
				mT__46(); 

				}
				break;
			case 16 :
				// Pseudo.g:1:100: T__47
				{
				mT__47(); 

				}
				break;
			case 17 :
				// Pseudo.g:1:106: T__48
				{
				mT__48(); 

				}
				break;
			case 18 :
				// Pseudo.g:1:112: T__49
				{
				mT__49(); 

				}
				break;
			case 19 :
				// Pseudo.g:1:118: T__50
				{
				mT__50(); 

				}
				break;
			case 20 :
				// Pseudo.g:1:124: T__51
				{
				mT__51(); 

				}
				break;
			case 21 :
				// Pseudo.g:1:130: T__52
				{
				mT__52(); 

				}
				break;
			case 22 :
				// Pseudo.g:1:136: T__53
				{
				mT__53(); 

				}
				break;
			case 23 :
				// Pseudo.g:1:142: T__54
				{
				mT__54(); 

				}
				break;
			case 24 :
				// Pseudo.g:1:148: T__55
				{
				mT__55(); 

				}
				break;
			case 25 :
				// Pseudo.g:1:154: T__56
				{
				mT__56(); 

				}
				break;
			case 26 :
				// Pseudo.g:1:160: INT
				{
				mINT(); 

				}
				break;
			case 27 :
				// Pseudo.g:1:164: SET
				{
				mSET(); 

				}
				break;
			case 28 :
				// Pseudo.g:1:168: ARRAY
				{
				mARRAY(); 

				}
				break;
			case 29 :
				// Pseudo.g:1:174: RETURNS
				{
				mRETURNS(); 

				}
				break;
			case 30 :
				// Pseudo.g:1:182: ENSURES
				{
				mENSURES(); 

				}
				break;
			case 31 :
				// Pseudo.g:1:190: REQUIRES
				{
				mREQUIRES(); 

				}
				break;
			case 32 :
				// Pseudo.g:1:199: DECREASES
				{
				mDECREASES(); 

				}
				break;
			case 33 :
				// Pseudo.g:1:209: FUNCTION
				{
				mFUNCTION(); 

				}
				break;
			case 34 :
				// Pseudo.g:1:218: ELSE
				{
				mELSE(); 

				}
				break;
			case 35 :
				// Pseudo.g:1:223: IF
				{
				mIF(); 

				}
				break;
			case 36 :
				// Pseudo.g:1:226: THEN
				{
				mTHEN(); 

				}
				break;
			case 37 :
				// Pseudo.g:1:231: WHILE
				{
				mWHILE(); 

				}
				break;
			case 38 :
				// Pseudo.g:1:237: VAR
				{
				mVAR(); 

				}
				break;
			case 39 :
				// Pseudo.g:1:241: NOT
				{
				mNOT(); 

				}
				break;
			case 40 :
				// Pseudo.g:1:245: CALL
				{
				mCALL(); 

				}
				break;
			case 41 :
				// Pseudo.g:1:250: INVARIANT
				{
				mINVARIANT(); 

				}
				break;
			case 42 :
				// Pseudo.g:1:260: ALL
				{
				mALL(); 

				}
				break;
			case 43 :
				// Pseudo.g:1:264: EX
				{
				mEX(); 

				}
				break;
			case 44 :
				// Pseudo.g:1:267: ASSIGN
				{
				mASSIGN(); 

				}
				break;
			case 45 :
				// Pseudo.g:1:274: ID
				{
				mID(); 

				}
				break;
			case 46 :
				// Pseudo.g:1:277: LIT
				{
				mLIT(); 

				}
				break;
			case 47 :
				// Pseudo.g:1:281: WS
				{
				mWS(); 

				}
				break;

		}
	}


	protected DFA3 dfa3 = new DFA3(this);
	static final String DFA3_eotS =
		"\4\uffff\1\44\1\46\2\uffff\1\50\1\uffff\1\52\1\54\1\56\2\uffff\3\40\3"+
		"\uffff\12\40\20\uffff\1\40\1\102\4\40\1\111\11\40\2\uffff\1\40\1\uffff"+
		"\1\40\1\126\2\40\1\131\1\40\1\uffff\1\133\6\40\1\142\1\143\3\40\1\uffff"+
		"\1\40\1\150\1\uffff\1\40\1\uffff\4\40\1\156\1\40\2\uffff\1\160\1\161\2"+
		"\40\1\uffff\1\40\1\165\3\40\1\uffff\1\171\2\uffff\3\40\1\uffff\3\40\1"+
		"\uffff\1\40\1\u0081\1\40\1\u0083\3\40\1\uffff\1\40\1\uffff\1\u0088\1\u0089"+
		"\1\u008a\1\u008b\4\uffff";
	static final String DFA3_eofS =
		"\u008c\uffff";
	static final String DFA3_minS =
		"\1\12\3\uffff\1\52\1\53\2\uffff\1\75\1\uffff\3\75\2\uffff\2\145\1\154"+
		"\3\uffff\1\146\1\145\1\162\1\145\1\165\2\150\1\141\1\157\2\141\17\uffff"+
		"\1\147\1\141\1\143\1\144\1\163\1\164\1\141\1\164\1\162\1\161\1\156\1\145"+
		"\1\151\1\162\1\164\1\154\2\uffff\1\151\1\uffff\1\162\1\141\1\165\1\145"+
		"\2\141\1\uffff\2\141\2\165\1\143\1\156\1\154\2\141\1\154\1\156\1\145\1"+
		"\uffff\1\162\1\141\1\uffff\1\162\1\uffff\1\171\1\162\1\151\1\164\1\141"+
		"\1\145\2\uffff\3\141\1\145\1\uffff\1\151\1\141\1\156\1\162\1\151\1\uffff"+
		"\1\141\2\uffff\2\163\1\141\1\uffff\1\163\1\145\1\157\1\uffff\1\145\1\141"+
		"\1\156\1\141\1\163\1\156\1\163\1\uffff\1\164\1\uffff\4\141\4\uffff";
	static final String DFA3_maxS =
		"\1\175\3\uffff\1\52\1\53\2\uffff\1\75\1\uffff\3\75\2\uffff\1\145\1\157"+
		"\1\156\3\uffff\1\156\1\145\1\162\1\145\1\165\2\150\1\141\1\157\1\141\1"+
		"\145\17\uffff\1\147\1\172\1\143\2\163\1\166\1\172\1\164\1\162\1\164\1"+
		"\156\1\145\1\151\1\162\1\164\1\154\2\uffff\1\151\1\uffff\1\162\1\172\1"+
		"\165\1\145\1\172\1\141\1\uffff\1\172\1\141\2\165\1\143\1\156\1\154\2\172"+
		"\1\154\1\156\1\145\1\uffff\1\162\1\172\1\uffff\1\162\1\uffff\1\171\1\162"+
		"\1\151\1\164\1\172\1\145\2\uffff\2\172\1\141\1\145\1\uffff\1\151\1\172"+
		"\1\156\1\162\1\151\1\uffff\1\172\2\uffff\2\163\1\141\1\uffff\1\163\1\145"+
		"\1\157\1\uffff\1\145\1\172\1\156\1\172\1\163\1\156\1\163\1\uffff\1\164"+
		"\1\uffff\4\172\4\uffff";
	static final String DFA3_acceptS =
		"\1\uffff\1\1\1\2\1\3\2\uffff\1\10\1\11\1\uffff\1\13\3\uffff\1\22\1\23"+
		"\3\uffff\1\27\1\30\1\31\13\uffff\1\55\1\56\1\57\1\5\1\4\1\7\1\6\1\54\1"+
		"\12\1\15\1\14\1\17\1\16\1\21\1\20\20\uffff\1\52\1\53\1\uffff\1\25\6\uffff"+
		"\1\43\14\uffff\1\26\2\uffff\1\32\1\uffff\1\33\6\uffff\1\46\1\47\4\uffff"+
		"\1\42\5\uffff\1\44\1\uffff\1\50\1\24\3\uffff\1\34\3\uffff\1\45\7\uffff"+
		"\1\36\1\uffff\1\35\4\uffff\1\37\1\41\1\40\1\51";
	static final String DFA3_specialS =
		"\u008c\uffff}>";
	static final String[] DFA3_transitionS = {
			"\1\42\2\uffff\1\42\22\uffff\1\42\5\uffff\1\1\1\uffff\1\2\1\3\1\4\1\5"+
			"\1\6\1\7\2\uffff\12\41\1\10\1\11\1\12\1\13\1\14\34\uffff\1\15\1\37\1"+
			"\16\3\uffff\1\27\1\17\1\36\1\20\1\21\1\31\2\40\1\25\4\40\1\35\3\40\1"+
			"\30\1\26\1\32\1\40\1\34\1\33\3\40\1\22\1\23\1\24",
			"",
			"",
			"",
			"\1\43",
			"\1\45",
			"",
			"",
			"\1\47",
			"",
			"\1\51",
			"\1\53",
			"\1\55",
			"",
			"",
			"\1\57",
			"\1\61\11\uffff\1\60",
			"\1\63\1\uffff\1\62",
			"",
			"",
			"",
			"\1\65\7\uffff\1\64",
			"\1\66",
			"\1\67",
			"\1\70",
			"\1\71",
			"\1\72",
			"\1\73",
			"\1\74",
			"\1\75",
			"\1\76",
			"\1\77\3\uffff\1\100",
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
			"",
			"",
			"",
			"\1\101",
			"\32\40",
			"\1\103",
			"\1\104\16\uffff\1\105",
			"\1\106",
			"\1\107\1\uffff\1\110",
			"\32\40",
			"\1\112",
			"\1\113",
			"\1\115\2\uffff\1\114",
			"\1\116",
			"\1\117",
			"\1\120",
			"\1\121",
			"\1\122",
			"\1\123",
			"",
			"",
			"\1\124",
			"",
			"\1\125",
			"\32\40",
			"\1\127",
			"\1\130",
			"\32\40",
			"\1\132",
			"",
			"\32\40",
			"\1\134",
			"\1\135",
			"\1\136",
			"\1\137",
			"\1\140",
			"\1\141",
			"\32\40",
			"\32\40",
			"\1\144",
			"\1\145",
			"\1\146",
			"",
			"\1\147",
			"\32\40",
			"",
			"\1\151",
			"",
			"\1\152",
			"\1\153",
			"\1\154",
			"\1\155",
			"\32\40",
			"\1\157",
			"",
			"",
			"\32\40",
			"\32\40",
			"\1\162",
			"\1\163",
			"",
			"\1\164",
			"\32\40",
			"\1\166",
			"\1\167",
			"\1\170",
			"",
			"\32\40",
			"",
			"",
			"\1\172",
			"\1\173",
			"\1\174",
			"",
			"\1\175",
			"\1\176",
			"\1\177",
			"",
			"\1\u0080",
			"\32\40",
			"\1\u0082",
			"\32\40",
			"\1\u0084",
			"\1\u0085",
			"\1\u0086",
			"",
			"\1\u0087",
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
			return "1:1: Tokens : ( T__32 | T__33 | T__34 | T__35 | T__36 | T__37 | T__38 | T__39 | T__40 | T__41 | T__42 | T__43 | T__44 | T__45 | T__46 | T__47 | T__48 | T__49 | T__50 | T__51 | T__52 | T__53 | T__54 | T__55 | T__56 | INT | SET | ARRAY | RETURNS | ENSURES | REQUIRES | DECREASES | FUNCTION | ELSE | IF | THEN | WHILE | VAR | NOT | CALL | INVARIANT | ALL | EX | ASSIGN | ID | LIT | WS );";
		}
	}

}
