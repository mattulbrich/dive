// $ANTLR 3.5.2 edu/kit/iti/algover/script/Script.g 2017-08-07 15:40:45

  package edu.kit.iti.algover.script;


@SuppressWarnings("all")
public class ScriptLexer extends Lexer {
	public static final int EOF=-1;
	public static final int T__33=33;
	public static final int T__34=34;
	public static final int T__35=35;
	public static final int T__36=36;
	public static final int T__37=37;
	public static final int T__38=38;
	public static final int T__39=39;
	public static final int T__40=40;
	public static final int APPLY=4;
	public static final int BEGIN=5;
	public static final int DAFNYEND=6;
	public static final int DAFNYTIMEOUT=7;
	public static final int END=8;
	public static final int FALSE=9;
	public static final int FILE=10;
	public static final int ID=11;
	public static final int IMPORT=12;
	public static final int INLINE=13;
	public static final int INT=14;
	public static final int KEYTIMEOUT=15;
	public static final int LIBRARY=16;
	public static final int LOOPUNROLL=17;
	public static final int MULTILINE_COMMENT=18;
	public static final int PATHSEP=19;
	public static final int POSTPONE=20;
	public static final int PREAMBLE=21;
	public static final int PROOF=22;
	public static final int PVC=23;
	public static final int QED=24;
	public static final int SET=25;
	public static final int SETTINGS=26;
	public static final int SINGLELINE_COMMENT=27;
	public static final int SUBSCRIPT=28;
	public static final int TIMEOUT=29;
	public static final int TRUE=30;
	public static final int VCG=31;
	public static final int WS=32;

	// delegates
	// delegators
	public Lexer[] getDelegates() {
		return new Lexer[] {};
	}

	public ScriptLexer() {} 
	public ScriptLexer(CharStream input) {
		this(input, new RecognizerSharedState());
	}
	public ScriptLexer(CharStream input, RecognizerSharedState state) {
		super(input,state);
	}
	@Override public String getGrammarFileName() { return "edu/kit/iti/algover/script/Script.g"; }

	// $ANTLR start "T__33"
	public final void mT__33() throws RecognitionException {
		try {
			int _type = T__33;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// edu/kit/iti/algover/script/Script.g:6:7: ( ',' )
			// edu/kit/iti/algover/script/Script.g:6:9: ','
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
	// $ANTLR end "T__33"

	// $ANTLR start "T__34"
	public final void mT__34() throws RecognitionException {
		try {
			int _type = T__34;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// edu/kit/iti/algover/script/Script.g:7:7: ( ':' )
			// edu/kit/iti/algover/script/Script.g:7:9: ':'
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
	// $ANTLR end "T__34"

	// $ANTLR start "T__35"
	public final void mT__35() throws RecognitionException {
		try {
			int _type = T__35;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// edu/kit/iti/algover/script/Script.g:8:7: ( ';' )
			// edu/kit/iti/algover/script/Script.g:8:9: ';'
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
	// $ANTLR end "T__35"

	// $ANTLR start "T__36"
	public final void mT__36() throws RecognitionException {
		try {
			int _type = T__36;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// edu/kit/iti/algover/script/Script.g:9:7: ( 'PVC_' )
			// edu/kit/iti/algover/script/Script.g:9:9: 'PVC_'
			{
			match("PVC_"); 

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
			// edu/kit/iti/algover/script/Script.g:10:7: ( '[' )
			// edu/kit/iti/algover/script/Script.g:10:9: '['
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
	// $ANTLR end "T__37"

	// $ANTLR start "T__38"
	public final void mT__38() throws RecognitionException {
		try {
			int _type = T__38;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// edu/kit/iti/algover/script/Script.g:11:7: ( ']' )
			// edu/kit/iti/algover/script/Script.g:11:9: ']'
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
	// $ANTLR end "T__38"

	// $ANTLR start "T__39"
	public final void mT__39() throws RecognitionException {
		try {
			int _type = T__39;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// edu/kit/iti/algover/script/Script.g:12:7: ( '{' )
			// edu/kit/iti/algover/script/Script.g:12:9: '{'
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
	// $ANTLR end "T__39"

	// $ANTLR start "T__40"
	public final void mT__40() throws RecognitionException {
		try {
			int _type = T__40;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// edu/kit/iti/algover/script/Script.g:13:7: ( '}' )
			// edu/kit/iti/algover/script/Script.g:13:9: '}'
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
	// $ANTLR end "T__40"

	// $ANTLR start "IMPORT"
	public final void mIMPORT() throws RecognitionException {
		try {
			int _type = IMPORT;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// edu/kit/iti/algover/script/Script.g:21:7: ( 'import' )
			// edu/kit/iti/algover/script/Script.g:21:9: 'import'
			{
			match("import"); 

			}

			state.type = _type;
			state.channel = _channel;
		}
		finally {
			// do for sure before leaving
		}
	}
	// $ANTLR end "IMPORT"

	// $ANTLR start "LIBRARY"
	public final void mLIBRARY() throws RecognitionException {
		try {
			int _type = LIBRARY;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// edu/kit/iti/algover/script/Script.g:22:8: ( 'lib' )
			// edu/kit/iti/algover/script/Script.g:22:10: 'lib'
			{
			match("lib"); 

			}

			state.type = _type;
			state.channel = _channel;
		}
		finally {
			// do for sure before leaving
		}
	}
	// $ANTLR end "LIBRARY"

	// $ANTLR start "PREAMBLE"
	public final void mPREAMBLE() throws RecognitionException {
		try {
			int _type = PREAMBLE;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// edu/kit/iti/algover/script/Script.g:23:9: ( 'preamble' )
			// edu/kit/iti/algover/script/Script.g:23:11: 'preamble'
			{
			match("preamble"); 

			}

			state.type = _type;
			state.channel = _channel;
		}
		finally {
			// do for sure before leaving
		}
	}
	// $ANTLR end "PREAMBLE"

	// $ANTLR start "SETTINGS"
	public final void mSETTINGS() throws RecognitionException {
		try {
			int _type = SETTINGS;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// edu/kit/iti/algover/script/Script.g:24:9: ( 'settings' )
			// edu/kit/iti/algover/script/Script.g:24:11: 'settings'
			{
			match("settings"); 

			}

			state.type = _type;
			state.channel = _channel;
		}
		finally {
			// do for sure before leaving
		}
	}
	// $ANTLR end "SETTINGS"

	// $ANTLR start "BEGIN"
	public final void mBEGIN() throws RecognitionException {
		try {
			int _type = BEGIN;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// edu/kit/iti/algover/script/Script.g:25:6: ( 'begin' )
			// edu/kit/iti/algover/script/Script.g:25:8: 'begin'
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
	// $ANTLR end "BEGIN"

	// $ANTLR start "END"
	public final void mEND() throws RecognitionException {
		try {
			int _type = END;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// edu/kit/iti/algover/script/Script.g:26:4: ( 'end' )
			// edu/kit/iti/algover/script/Script.g:26:6: 'end'
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
	// $ANTLR end "END"

	// $ANTLR start "TIMEOUT"
	public final void mTIMEOUT() throws RecognitionException {
		try {
			int _type = TIMEOUT;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// edu/kit/iti/algover/script/Script.g:27:8: ( 'timeout' )
			// edu/kit/iti/algover/script/Script.g:27:10: 'timeout'
			{
			match("timeout"); 

			}

			state.type = _type;
			state.channel = _channel;
		}
		finally {
			// do for sure before leaving
		}
	}
	// $ANTLR end "TIMEOUT"

	// $ANTLR start "TRUE"
	public final void mTRUE() throws RecognitionException {
		try {
			int _type = TRUE;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// edu/kit/iti/algover/script/Script.g:28:5: ( 'true' )
			// edu/kit/iti/algover/script/Script.g:28:7: 'true'
			{
			match("true"); 

			}

			state.type = _type;
			state.channel = _channel;
		}
		finally {
			// do for sure before leaving
		}
	}
	// $ANTLR end "TRUE"

	// $ANTLR start "FALSE"
	public final void mFALSE() throws RecognitionException {
		try {
			int _type = FALSE;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// edu/kit/iti/algover/script/Script.g:29:6: ( 'false' )
			// edu/kit/iti/algover/script/Script.g:29:8: 'false'
			{
			match("false"); 

			}

			state.type = _type;
			state.channel = _channel;
		}
		finally {
			// do for sure before leaving
		}
	}
	// $ANTLR end "FALSE"

	// $ANTLR start "LOOPUNROLL"
	public final void mLOOPUNROLL() throws RecognitionException {
		try {
			int _type = LOOPUNROLL;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// edu/kit/iti/algover/script/Script.g:30:11: ( 'loopunrolling' )
			// edu/kit/iti/algover/script/Script.g:30:13: 'loopunrolling'
			{
			match("loopunrolling"); 

			}

			state.type = _type;
			state.channel = _channel;
		}
		finally {
			// do for sure before leaving
		}
	}
	// $ANTLR end "LOOPUNROLL"

	// $ANTLR start "INLINE"
	public final void mINLINE() throws RecognitionException {
		try {
			int _type = INLINE;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// edu/kit/iti/algover/script/Script.g:31:7: ( 'inline methods' )
			// edu/kit/iti/algover/script/Script.g:31:9: 'inline methods'
			{
			match("inline methods"); 

			}

			state.type = _type;
			state.channel = _channel;
		}
		finally {
			// do for sure before leaving
		}
	}
	// $ANTLR end "INLINE"

	// $ANTLR start "DAFNYEND"
	public final void mDAFNYEND() throws RecognitionException {
		try {
			int _type = DAFNYEND;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// edu/kit/iti/algover/script/Script.g:32:9: ( '.dfy' )
			// edu/kit/iti/algover/script/Script.g:32:10: '.dfy'
			{
			match(".dfy"); 

			}

			state.type = _type;
			state.channel = _channel;
		}
		finally {
			// do for sure before leaving
		}
	}
	// $ANTLR end "DAFNYEND"

	// $ANTLR start "FILE"
	public final void mFILE() throws RecognitionException {
		try {
			int _type = FILE;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// edu/kit/iti/algover/script/Script.g:33:5: ( 'file' )
			// edu/kit/iti/algover/script/Script.g:33:7: 'file'
			{
			match("file"); 

			}

			state.type = _type;
			state.channel = _channel;
		}
		finally {
			// do for sure before leaving
		}
	}
	// $ANTLR end "FILE"

	// $ANTLR start "SUBSCRIPT"
	public final void mSUBSCRIPT() throws RecognitionException {
		try {
			int _type = SUBSCRIPT;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// edu/kit/iti/algover/script/Script.g:34:10: ( 'script for' )
			// edu/kit/iti/algover/script/Script.g:34:12: 'script for'
			{
			match("script for"); 

			}

			state.type = _type;
			state.channel = _channel;
		}
		finally {
			// do for sure before leaving
		}
	}
	// $ANTLR end "SUBSCRIPT"

	// $ANTLR start "PVC"
	public final void mPVC() throws RecognitionException {
		try {
			int _type = PVC;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// edu/kit/iti/algover/script/Script.g:35:5: ( 'PVC' )
			// edu/kit/iti/algover/script/Script.g:35:7: 'PVC'
			{
			match("PVC"); 

			}

			state.type = _type;
			state.channel = _channel;
		}
		finally {
			// do for sure before leaving
		}
	}
	// $ANTLR end "PVC"

	// $ANTLR start "SET"
	public final void mSET() throws RecognitionException {
		try {
			int _type = SET;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// edu/kit/iti/algover/script/Script.g:36:5: ( 'set' )
			// edu/kit/iti/algover/script/Script.g:36:7: 'set'
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

	// $ANTLR start "APPLY"
	public final void mAPPLY() throws RecognitionException {
		try {
			int _type = APPLY;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// edu/kit/iti/algover/script/Script.g:37:6: ( 'apply' )
			// edu/kit/iti/algover/script/Script.g:37:8: 'apply'
			{
			match("apply"); 

			}

			state.type = _type;
			state.channel = _channel;
		}
		finally {
			// do for sure before leaving
		}
	}
	// $ANTLR end "APPLY"

	// $ANTLR start "VCG"
	public final void mVCG() throws RecognitionException {
		try {
			int _type = VCG;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// edu/kit/iti/algover/script/Script.g:38:4: ( 'VCG' )
			// edu/kit/iti/algover/script/Script.g:38:6: 'VCG'
			{
			match("VCG"); 

			}

			state.type = _type;
			state.channel = _channel;
		}
		finally {
			// do for sure before leaving
		}
	}
	// $ANTLR end "VCG"

	// $ANTLR start "POSTPONE"
	public final void mPOSTPONE() throws RecognitionException {
		try {
			int _type = POSTPONE;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// edu/kit/iti/algover/script/Script.g:39:9: ( 'postpone' )
			// edu/kit/iti/algover/script/Script.g:39:11: 'postpone'
			{
			match("postpone"); 

			}

			state.type = _type;
			state.channel = _channel;
		}
		finally {
			// do for sure before leaving
		}
	}
	// $ANTLR end "POSTPONE"

	// $ANTLR start "PROOF"
	public final void mPROOF() throws RecognitionException {
		try {
			int _type = PROOF;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// edu/kit/iti/algover/script/Script.g:40:6: ( 'Proof' )
			// edu/kit/iti/algover/script/Script.g:40:7: 'Proof'
			{
			match("Proof"); 

			}

			state.type = _type;
			state.channel = _channel;
		}
		finally {
			// do for sure before leaving
		}
	}
	// $ANTLR end "PROOF"

	// $ANTLR start "QED"
	public final void mQED() throws RecognitionException {
		try {
			int _type = QED;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// edu/kit/iti/algover/script/Script.g:41:4: ( 'Qed' )
			// edu/kit/iti/algover/script/Script.g:41:6: 'Qed'
			{
			match("Qed"); 

			}

			state.type = _type;
			state.channel = _channel;
		}
		finally {
			// do for sure before leaving
		}
	}
	// $ANTLR end "QED"

	// $ANTLR start "KEYTIMEOUT"
	public final void mKEYTIMEOUT() throws RecognitionException {
		try {
			int _type = KEYTIMEOUT;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// edu/kit/iti/algover/script/Script.g:42:11: ( 'key_timeout' )
			// edu/kit/iti/algover/script/Script.g:42:13: 'key_timeout'
			{
			match("key_timeout"); 

			}

			state.type = _type;
			state.channel = _channel;
		}
		finally {
			// do for sure before leaving
		}
	}
	// $ANTLR end "KEYTIMEOUT"

	// $ANTLR start "DAFNYTIMEOUT"
	public final void mDAFNYTIMEOUT() throws RecognitionException {
		try {
			int _type = DAFNYTIMEOUT;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// edu/kit/iti/algover/script/Script.g:43:13: ( 'dafny_timeout' )
			// edu/kit/iti/algover/script/Script.g:43:14: 'dafny_timeout'
			{
			match("dafny_timeout"); 

			}

			state.type = _type;
			state.channel = _channel;
		}
		finally {
			// do for sure before leaving
		}
	}
	// $ANTLR end "DAFNYTIMEOUT"

	// $ANTLR start "ID"
	public final void mID() throws RecognitionException {
		try {
			int _type = ID;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// edu/kit/iti/algover/script/Script.g:45:4: ( ( 'a' .. 'z' | 'A' .. 'Z' | '_' ) ( 'a' .. 'z' | 'A' .. 'Z' | '0' .. '9' | '_' )* )
			// edu/kit/iti/algover/script/Script.g:45:6: ( 'a' .. 'z' | 'A' .. 'Z' | '_' ) ( 'a' .. 'z' | 'A' .. 'Z' | '0' .. '9' | '_' )*
			{
			if ( (input.LA(1) >= 'A' && input.LA(1) <= 'Z')||input.LA(1)=='_'||(input.LA(1) >= 'a' && input.LA(1) <= 'z') ) {
				input.consume();
			}
			else {
				MismatchedSetException mse = new MismatchedSetException(null,input);
				recover(mse);
				throw mse;
			}
			// edu/kit/iti/algover/script/Script.g:45:38: ( 'a' .. 'z' | 'A' .. 'Z' | '0' .. '9' | '_' )*
			loop1:
			while (true) {
				int alt1=2;
				int LA1_0 = input.LA(1);
				if ( ((LA1_0 >= '0' && LA1_0 <= '9')||(LA1_0 >= 'A' && LA1_0 <= 'Z')||LA1_0=='_'||(LA1_0 >= 'a' && LA1_0 <= 'z')) ) {
					alt1=1;
				}

				switch (alt1) {
				case 1 :
					// edu/kit/iti/algover/script/Script.g:
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
	// $ANTLR end "ID"

	// $ANTLR start "INT"
	public final void mINT() throws RecognitionException {
		try {
			int _type = INT;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// edu/kit/iti/algover/script/Script.g:46:5: ( ( '0' .. '9' ) ( '0' .. '9' )* )
			// edu/kit/iti/algover/script/Script.g:46:7: ( '0' .. '9' ) ( '0' .. '9' )*
			{
			if ( (input.LA(1) >= '0' && input.LA(1) <= '9') ) {
				input.consume();
			}
			else {
				MismatchedSetException mse = new MismatchedSetException(null,input);
				recover(mse);
				throw mse;
			}
			// edu/kit/iti/algover/script/Script.g:46:21: ( '0' .. '9' )*
			loop2:
			while (true) {
				int alt2=2;
				int LA2_0 = input.LA(1);
				if ( ((LA2_0 >= '0' && LA2_0 <= '9')) ) {
					alt2=1;
				}

				switch (alt2) {
				case 1 :
					// edu/kit/iti/algover/script/Script.g:
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

			state.type = _type;
			state.channel = _channel;
		}
		finally {
			// do for sure before leaving
		}
	}
	// $ANTLR end "INT"

	// $ANTLR start "PATHSEP"
	public final void mPATHSEP() throws RecognitionException {
		try {
			int _type = PATHSEP;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// edu/kit/iti/algover/script/Script.g:47:9: ( '/' | '..' | '.' )
			int alt3=3;
			int LA3_0 = input.LA(1);
			if ( (LA3_0=='/') ) {
				alt3=1;
			}
			else if ( (LA3_0=='.') ) {
				int LA3_2 = input.LA(2);
				if ( (LA3_2=='.') ) {
					alt3=2;
				}

				else {
					alt3=3;
				}

			}

			else {
				NoViableAltException nvae =
					new NoViableAltException("", 3, 0, input);
				throw nvae;
			}

			switch (alt3) {
				case 1 :
					// edu/kit/iti/algover/script/Script.g:47:11: '/'
					{
					match('/'); 
					}
					break;
				case 2 :
					// edu/kit/iti/algover/script/Script.g:47:15: '..'
					{
					match("modules/core");

					}
					break;
				case 3 :
					// edu/kit/iti/algover/script/Script.g:47:20: '.'
					{
					match('.'); 
					}
					break;

			}
			state.type = _type;
			state.channel = _channel;
		}
		finally {
			// do for sure before leaving
		}
	}
	// $ANTLR end "PATHSEP"

	// $ANTLR start "WS"
	public final void mWS() throws RecognitionException {
		try {
			int _type = WS;
			int _channel = DEFAULT_TOKEN_CHANNEL;
			// edu/kit/iti/algover/script/Script.g:49:4: ( ( ' ' | '\\n' | '\\r' ) )
			// edu/kit/iti/algover/script/Script.g:49:6: ( ' ' | '\\n' | '\\r' )
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
			// edu/kit/iti/algover/script/Script.g:50:19: ( '//' (~ ( '\\r' | '\\n' ) )* )
			// edu/kit/iti/algover/script/Script.g:50:21: '//' (~ ( '\\r' | '\\n' ) )*
			{
			match("//"); 

			// edu/kit/iti/algover/script/Script.g:50:26: (~ ( '\\r' | '\\n' ) )*
			loop4:
			while (true) {
				int alt4=2;
				int LA4_0 = input.LA(1);
				if ( ((LA4_0 >= '\u0000' && LA4_0 <= '\t')||(LA4_0 >= '\u000B' && LA4_0 <= '\f')||(LA4_0 >= '\u000E' && LA4_0 <= '\uFFFF')) ) {
					alt4=1;
				}

				switch (alt4) {
				case 1 :
					// edu/kit/iti/algover/script/Script.g:
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
					break loop4;
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
			// edu/kit/iti/algover/script/Script.g:51:18: ( '/*' ( . )* '*/' )
			// edu/kit/iti/algover/script/Script.g:51:20: '/*' ( . )* '*/'
			{
			match("/*"); 

			// edu/kit/iti/algover/script/Script.g:51:25: ( . )*
			loop5:
			while (true) {
				int alt5=2;
				int LA5_0 = input.LA(1);
				if ( (LA5_0=='*') ) {
					int LA5_1 = input.LA(2);
					if ( (LA5_1=='/') ) {
						alt5=2;
					}
					else if ( ((LA5_1 >= '\u0000' && LA5_1 <= '.')||(LA5_1 >= '0' && LA5_1 <= '\uFFFF')) ) {
						alt5=1;
					}

				}
				else if ( ((LA5_0 >= '\u0000' && LA5_0 <= ')')||(LA5_0 >= '+' && LA5_0 <= '\uFFFF')) ) {
					alt5=1;
				}

				switch (alt5) {
				case 1 :
					// edu/kit/iti/algover/script/Script.g:51:25: .
					{
					matchAny(); 
					}
					break;

				default :
					break loop5;
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
		// edu/kit/iti/algover/script/Script.g:1:8: ( T__33 | T__34 | T__35 | T__36 | T__37 | T__38 | T__39 | T__40 | IMPORT | LIBRARY | PREAMBLE | SETTINGS | BEGIN | END | TIMEOUT | TRUE | FALSE | LOOPUNROLL | INLINE | DAFNYEND | FILE | SUBSCRIPT | PVC | SET | APPLY | VCG | POSTPONE | PROOF | QED | KEYTIMEOUT | DAFNYTIMEOUT | ID | INT | PATHSEP | WS | SINGLELINE_COMMENT | MULTILINE_COMMENT )
		int alt6=37;
		alt6 = dfa6.predict(input);
		switch (alt6) {
			case 1 :
				// edu/kit/iti/algover/script/Script.g:1:10: T__33
				{
				mT__33(); 

				}
				break;
			case 2 :
				// edu/kit/iti/algover/script/Script.g:1:16: T__34
				{
				mT__34(); 

				}
				break;
			case 3 :
				// edu/kit/iti/algover/script/Script.g:1:22: T__35
				{
				mT__35(); 

				}
				break;
			case 4 :
				// edu/kit/iti/algover/script/Script.g:1:28: T__36
				{
				mT__36(); 

				}
				break;
			case 5 :
				// edu/kit/iti/algover/script/Script.g:1:34: T__37
				{
				mT__37(); 

				}
				break;
			case 6 :
				// edu/kit/iti/algover/script/Script.g:1:40: T__38
				{
				mT__38(); 

				}
				break;
			case 7 :
				// edu/kit/iti/algover/script/Script.g:1:46: T__39
				{
				mT__39(); 

				}
				break;
			case 8 :
				// edu/kit/iti/algover/script/Script.g:1:52: T__40
				{
				mT__40(); 

				}
				break;
			case 9 :
				// edu/kit/iti/algover/script/Script.g:1:58: IMPORT
				{
				mIMPORT(); 

				}
				break;
			case 10 :
				// edu/kit/iti/algover/script/Script.g:1:65: LIBRARY
				{
				mLIBRARY(); 

				}
				break;
			case 11 :
				// edu/kit/iti/algover/script/Script.g:1:73: PREAMBLE
				{
				mPREAMBLE(); 

				}
				break;
			case 12 :
				// edu/kit/iti/algover/script/Script.g:1:82: SETTINGS
				{
				mSETTINGS(); 

				}
				break;
			case 13 :
				// edu/kit/iti/algover/script/Script.g:1:91: BEGIN
				{
				mBEGIN(); 

				}
				break;
			case 14 :
				// edu/kit/iti/algover/script/Script.g:1:97: END
				{
				mEND(); 

				}
				break;
			case 15 :
				// edu/kit/iti/algover/script/Script.g:1:101: TIMEOUT
				{
				mTIMEOUT(); 

				}
				break;
			case 16 :
				// edu/kit/iti/algover/script/Script.g:1:109: TRUE
				{
				mTRUE(); 

				}
				break;
			case 17 :
				// edu/kit/iti/algover/script/Script.g:1:114: FALSE
				{
				mFALSE(); 

				}
				break;
			case 18 :
				// edu/kit/iti/algover/script/Script.g:1:120: LOOPUNROLL
				{
				mLOOPUNROLL(); 

				}
				break;
			case 19 :
				// edu/kit/iti/algover/script/Script.g:1:131: INLINE
				{
				mINLINE(); 

				}
				break;
			case 20 :
				// edu/kit/iti/algover/script/Script.g:1:138: DAFNYEND
				{
				mDAFNYEND(); 

				}
				break;
			case 21 :
				// edu/kit/iti/algover/script/Script.g:1:147: FILE
				{
				mFILE(); 

				}
				break;
			case 22 :
				// edu/kit/iti/algover/script/Script.g:1:152: SUBSCRIPT
				{
				mSUBSCRIPT(); 

				}
				break;
			case 23 :
				// edu/kit/iti/algover/script/Script.g:1:162: PVC
				{
				mPVC(); 

				}
				break;
			case 24 :
				// edu/kit/iti/algover/script/Script.g:1:166: SET
				{
				mSET(); 

				}
				break;
			case 25 :
				// edu/kit/iti/algover/script/Script.g:1:170: APPLY
				{
				mAPPLY(); 

				}
				break;
			case 26 :
				// edu/kit/iti/algover/script/Script.g:1:176: VCG
				{
				mVCG(); 

				}
				break;
			case 27 :
				// edu/kit/iti/algover/script/Script.g:1:180: POSTPONE
				{
				mPOSTPONE(); 

				}
				break;
			case 28 :
				// edu/kit/iti/algover/script/Script.g:1:189: PROOF
				{
				mPROOF(); 

				}
				break;
			case 29 :
				// edu/kit/iti/algover/script/Script.g:1:195: QED
				{
				mQED(); 

				}
				break;
			case 30 :
				// edu/kit/iti/algover/script/Script.g:1:199: KEYTIMEOUT
				{
				mKEYTIMEOUT(); 

				}
				break;
			case 31 :
				// edu/kit/iti/algover/script/Script.g:1:210: DAFNYTIMEOUT
				{
				mDAFNYTIMEOUT(); 

				}
				break;
			case 32 :
				// edu/kit/iti/algover/script/Script.g:1:223: ID
				{
				mID(); 

				}
				break;
			case 33 :
				// edu/kit/iti/algover/script/Script.g:1:226: INT
				{
				mINT(); 

				}
				break;
			case 34 :
				// edu/kit/iti/algover/script/Script.g:1:230: PATHSEP
				{
				mPATHSEP(); 

				}
				break;
			case 35 :
				// edu/kit/iti/algover/script/Script.g:1:238: WS
				{
				mWS(); 

				}
				break;
			case 36 :
				// edu/kit/iti/algover/script/Script.g:1:241: SINGLELINE_COMMENT
				{
				mSINGLELINE_COMMENT(); 

				}
				break;
			case 37 :
				// edu/kit/iti/algover/script/Script.g:1:260: MULTILINE_COMMENT
				{
				mMULTILINE_COMMENT(); 

				}
				break;

		}
	}


	protected DFA6 dfa6 = new DFA6(this);
	static final String DFA6_eotS =
		"\4\uffff\1\27\4\uffff\10\27\1\54\5\27\2\uffff\1\54\1\uffff\20\27\2\uffff"+
		"\5\27\2\uffff\1\112\3\27\1\116\3\27\1\123\2\27\1\126\5\27\1\134\1\135"+
		"\2\27\1\140\1\uffff\3\27\1\uffff\4\27\1\uffff\2\27\1\uffff\1\27\1\153"+
		"\1\27\1\155\1\27\2\uffff\2\27\1\uffff\1\161\7\27\1\171\1\27\1\uffff\1"+
		"\173\1\uffff\1\174\2\27\1\uffff\1\177\6\27\1\uffff\1\27\2\uffff\2\27\2"+
		"\uffff\4\27\1\uffff\1\u008d\3\27\1\u0091\1\u0092\1\u0093\1\uffff\3\27"+
		"\3\uffff\6\27\1\u009d\2\27\1\uffff\1\27\1\u00a1\1\u00a2\2\uffff";
	static final String DFA6_eofS =
		"\u00a3\uffff";
	static final String DFA6_minS =
		"\1\12\3\uffff\1\126\4\uffff\1\155\1\151\1\157\1\143\1\145\1\156\1\151"+
		"\1\141\1\144\1\160\1\103\2\145\1\141\2\uffff\1\52\1\uffff\1\103\1\157"+
		"\1\160\1\154\1\142\1\157\1\145\1\163\1\164\1\162\1\147\1\144\1\155\1\165"+
		"\2\154\2\uffff\1\160\1\107\1\144\1\171\1\146\2\uffff\1\60\2\157\1\151"+
		"\1\60\1\160\1\141\1\164\1\60\2\151\1\60\2\145\1\163\1\145\1\154\2\60\1"+
		"\137\1\156\1\60\1\uffff\1\146\1\162\1\156\1\uffff\1\165\1\155\1\160\1"+
		"\151\1\uffff\1\160\1\156\1\uffff\1\157\1\60\1\145\1\60\1\171\2\uffff\1"+
		"\164\1\171\1\uffff\1\60\1\164\1\145\1\156\1\142\1\157\1\156\1\164\1\60"+
		"\1\165\1\uffff\1\60\1\uffff\1\60\1\151\1\137\1\uffff\1\60\1\40\1\162\1"+
		"\154\1\156\1\147\1\40\1\uffff\1\164\2\uffff\1\155\1\164\2\uffff\1\157"+
		"\2\145\1\163\1\uffff\1\60\1\145\1\151\1\154\3\60\1\uffff\1\157\1\155\1"+
		"\154\3\uffff\1\165\1\145\1\151\1\164\1\157\1\156\1\60\1\165\1\147\1\uffff"+
		"\1\164\2\60\2\uffff";
	static final String DFA6_maxS =
		"\1\175\3\uffff\1\162\4\uffff\1\156\1\157\1\162\2\145\1\156\1\162\1\151"+
		"\1\144\1\160\1\103\2\145\1\141\2\uffff\1\57\1\uffff\1\103\1\157\1\160"+
		"\1\154\1\142\1\157\1\145\1\163\1\164\1\162\1\147\1\144\1\155\1\165\2\154"+
		"\2\uffff\1\160\1\107\1\144\1\171\1\146\2\uffff\1\172\2\157\1\151\1\172"+
		"\1\160\1\141\1\164\1\172\2\151\1\172\2\145\1\163\1\145\1\154\2\172\1\137"+
		"\1\156\1\172\1\uffff\1\146\1\162\1\156\1\uffff\1\165\1\155\1\160\1\151"+
		"\1\uffff\1\160\1\156\1\uffff\1\157\1\172\1\145\1\172\1\171\2\uffff\1\164"+
		"\1\171\1\uffff\1\172\1\164\1\145\1\156\1\142\1\157\1\156\1\164\1\172\1"+
		"\165\1\uffff\1\172\1\uffff\1\172\1\151\1\137\1\uffff\1\172\1\40\1\162"+
		"\1\154\1\156\1\147\1\40\1\uffff\1\164\2\uffff\1\155\1\164\2\uffff\1\157"+
		"\2\145\1\163\1\uffff\1\172\1\145\1\151\1\154\3\172\1\uffff\1\157\1\155"+
		"\1\154\3\uffff\1\165\1\145\1\151\1\164\1\157\1\156\1\172\1\165\1\147\1"+
		"\uffff\1\164\2\172\2\uffff";
	static final String DFA6_acceptS =
		"\1\uffff\1\1\1\2\1\3\1\uffff\1\5\1\6\1\7\1\10\16\uffff\1\40\1\41\1\uffff"+
		"\1\43\20\uffff\1\24\1\42\5\uffff\1\44\1\45\26\uffff\1\27\3\uffff\1\12"+
		"\4\uffff\1\30\2\uffff\1\16\5\uffff\1\32\1\35\2\uffff\1\4\12\uffff\1\20"+
		"\1\uffff\1\25\3\uffff\1\34\7\uffff\1\15\1\uffff\1\21\1\31\2\uffff\1\11"+
		"\1\23\4\uffff\1\26\7\uffff\1\17\3\uffff\1\13\1\33\1\14\11\uffff\1\36\3"+
		"\uffff\1\22\1\37";
	static final String DFA6_specialS =
		"\u00a3\uffff}>";
	static final String[] DFA6_transitionS = {
			"\1\32\2\uffff\1\32\22\uffff\1\32\13\uffff\1\1\1\uffff\1\21\1\31\12\30"+
			"\1\2\1\3\5\uffff\17\27\1\4\1\24\4\27\1\23\4\27\1\5\1\uffff\1\6\1\uffff"+
			"\1\27\1\uffff\1\22\1\15\1\27\1\26\1\16\1\20\2\27\1\11\1\27\1\25\1\12"+
			"\3\27\1\13\2\27\1\14\1\17\6\27\1\7\1\uffff\1\10",
			"",
			"",
			"",
			"\1\33\33\uffff\1\34",
			"",
			"",
			"",
			"",
			"\1\35\1\36",
			"\1\37\5\uffff\1\40",
			"\1\42\2\uffff\1\41",
			"\1\44\1\uffff\1\43",
			"\1\45",
			"\1\46",
			"\1\47\10\uffff\1\50",
			"\1\51\7\uffff\1\52",
			"\1\53",
			"\1\55",
			"\1\56",
			"\1\57",
			"\1\60",
			"\1\61",
			"",
			"",
			"\1\63\4\uffff\1\62",
			"",
			"\1\64",
			"\1\65",
			"\1\66",
			"\1\67",
			"\1\70",
			"\1\71",
			"\1\72",
			"\1\73",
			"\1\74",
			"\1\75",
			"\1\76",
			"\1\77",
			"\1\100",
			"\1\101",
			"\1\102",
			"\1\103",
			"",
			"",
			"\1\104",
			"\1\105",
			"\1\106",
			"\1\107",
			"\1\110",
			"",
			"",
			"\12\27\7\uffff\32\27\4\uffff\1\111\1\uffff\32\27",
			"\1\113",
			"\1\114",
			"\1\115",
			"\12\27\7\uffff\32\27\4\uffff\1\27\1\uffff\32\27",
			"\1\117",
			"\1\120",
			"\1\121",
			"\12\27\7\uffff\32\27\4\uffff\1\27\1\uffff\23\27\1\122\6\27",
			"\1\124",
			"\1\125",
			"\12\27\7\uffff\32\27\4\uffff\1\27\1\uffff\32\27",
			"\1\127",
			"\1\130",
			"\1\131",
			"\1\132",
			"\1\133",
			"\12\27\7\uffff\32\27\4\uffff\1\27\1\uffff\32\27",
			"\12\27\7\uffff\32\27\4\uffff\1\27\1\uffff\32\27",
			"\1\136",
			"\1\137",
			"\12\27\7\uffff\32\27\4\uffff\1\27\1\uffff\32\27",
			"",
			"\1\141",
			"\1\142",
			"\1\143",
			"",
			"\1\144",
			"\1\145",
			"\1\146",
			"\1\147",
			"",
			"\1\150",
			"\1\151",
			"",
			"\1\152",
			"\12\27\7\uffff\32\27\4\uffff\1\27\1\uffff\32\27",
			"\1\154",
			"\12\27\7\uffff\32\27\4\uffff\1\27\1\uffff\32\27",
			"\1\156",
			"",
			"",
			"\1\157",
			"\1\160",
			"",
			"\12\27\7\uffff\32\27\4\uffff\1\27\1\uffff\32\27",
			"\1\162",
			"\1\163",
			"\1\164",
			"\1\165",
			"\1\166",
			"\1\167",
			"\1\170",
			"\12\27\7\uffff\32\27\4\uffff\1\27\1\uffff\32\27",
			"\1\172",
			"",
			"\12\27\7\uffff\32\27\4\uffff\1\27\1\uffff\32\27",
			"",
			"\12\27\7\uffff\32\27\4\uffff\1\27\1\uffff\32\27",
			"\1\175",
			"\1\176",
			"",
			"\12\27\7\uffff\32\27\4\uffff\1\27\1\uffff\32\27",
			"\1\u0080",
			"\1\u0081",
			"\1\u0082",
			"\1\u0083",
			"\1\u0084",
			"\1\u0085",
			"",
			"\1\u0086",
			"",
			"",
			"\1\u0087",
			"\1\u0088",
			"",
			"",
			"\1\u0089",
			"\1\u008a",
			"\1\u008b",
			"\1\u008c",
			"",
			"\12\27\7\uffff\32\27\4\uffff\1\27\1\uffff\32\27",
			"\1\u008e",
			"\1\u008f",
			"\1\u0090",
			"\12\27\7\uffff\32\27\4\uffff\1\27\1\uffff\32\27",
			"\12\27\7\uffff\32\27\4\uffff\1\27\1\uffff\32\27",
			"\12\27\7\uffff\32\27\4\uffff\1\27\1\uffff\32\27",
			"",
			"\1\u0094",
			"\1\u0095",
			"\1\u0096",
			"",
			"",
			"",
			"\1\u0097",
			"\1\u0098",
			"\1\u0099",
			"\1\u009a",
			"\1\u009b",
			"\1\u009c",
			"\12\27\7\uffff\32\27\4\uffff\1\27\1\uffff\32\27",
			"\1\u009e",
			"\1\u009f",
			"",
			"\1\u00a0",
			"\12\27\7\uffff\32\27\4\uffff\1\27\1\uffff\32\27",
			"\12\27\7\uffff\32\27\4\uffff\1\27\1\uffff\32\27",
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
			return "1:1: Tokens : ( T__33 | T__34 | T__35 | T__36 | T__37 | T__38 | T__39 | T__40 | IMPORT | LIBRARY | PREAMBLE | SETTINGS | BEGIN | END | TIMEOUT | TRUE | FALSE | LOOPUNROLL | INLINE | DAFNYEND | FILE | SUBSCRIPT | PVC | SET | APPLY | VCG | POSTPONE | PROOF | QED | KEYTIMEOUT | DAFNYTIMEOUT | ID | INT | PATHSEP | WS | SINGLELINE_COMMENT | MULTILINE_COMMENT );";
		}
	}

}
