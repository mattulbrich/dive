// $ANTLR 3.5.2 edu/kit/iti/algover/script/Script.g 2017-08-07 15:40:45

  package edu.kit.iti.algover.script;


@SuppressWarnings("all")
public class ScriptParser extends Parser {
	public static final String[] tokenNames = new String[] {
		"<invalid>", "<EOR>", "<DOWN>", "<UP>", "APPLY", "BEGIN", "DAFNYEND", 
		"DAFNYTIMEOUT", "END", "FALSE", "FILE", "ID", "IMPORT", "INLINE", "INT", 
		"KEYTIMEOUT", "LIBRARY", "LOOPUNROLL", "MULTILINE_COMMENT", "PATHSEP", 
		"POSTPONE", "PREAMBLE", "PROOF", "PVC", "QED", "SET", "SETTINGS", "SINGLELINE_COMMENT", 
		"SUBSCRIPT", "TIMEOUT", "TRUE", "VCG", "WS", "','", "':'", "';'", "'PVC_'", 
		"'['", "']'", "'{'", "'}'"
	};
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
	public Parser[] getDelegates() {
		return new Parser[] {};
	}

	// delegators


	public ScriptParser(TokenStream input) {
		this(input, new RecognizerSharedState());
	}
	public ScriptParser(TokenStream input, RecognizerSharedState state) {
		super(input, state);
	}

	protected TreeAdaptor adaptor = new CommonTreeAdaptor();

	public void setTreeAdaptor(TreeAdaptor adaptor) {
		this.adaptor = adaptor;
	}
	public TreeAdaptor getTreeAdaptor() {
		return adaptor;
	}
	@Override public String[] getTokenNames() { return ScriptParser.tokenNames; }
	@Override public String getGrammarFileName() { return "edu/kit/iti/algover/script/Script.g"; }


	public static class preamble_return extends ParserRuleReturnScope {
		ScriptTree tree;
		@Override
		public ScriptTree getTree() { return tree; }
	};


	// $ANTLR start "preamble"
	// edu/kit/iti/algover/script/Script.g:53:1: preamble : PREAMBLE BEGIN ! ( importDafny ';' !| importLibs ';' !| sets )+ END ! ( pvcscripts )* EOF ;
	public final ScriptParser.preamble_return preamble() throws RecognitionException {
		ScriptParser.preamble_return retval = new ScriptParser.preamble_return();
		retval.start = input.LT(1);

		ScriptTree root_0 = null;

		Token PREAMBLE1=null;
		Token BEGIN2=null;
		Token char_literal4=null;
		Token char_literal6=null;
		Token END8=null;
		Token EOF10=null;
		ParserRuleReturnScope importDafny3 =null;
		ParserRuleReturnScope importLibs5 =null;
		ParserRuleReturnScope sets7 =null;
		ParserRuleReturnScope pvcscripts9 =null;

		ScriptTree PREAMBLE1_tree=null;
		ScriptTree BEGIN2_tree=null;
		ScriptTree char_literal4_tree=null;
		ScriptTree char_literal6_tree=null;
		ScriptTree END8_tree=null;
		ScriptTree EOF10_tree=null;

		try {
			// edu/kit/iti/algover/script/Script.g:53:9: ( PREAMBLE BEGIN ! ( importDafny ';' !| importLibs ';' !| sets )+ END ! ( pvcscripts )* EOF )
			// edu/kit/iti/algover/script/Script.g:54:3: PREAMBLE BEGIN ! ( importDafny ';' !| importLibs ';' !| sets )+ END ! ( pvcscripts )* EOF
			{
			root_0 = (ScriptTree)adaptor.nil();


			PREAMBLE1=(Token)match(input,PREAMBLE,FOLLOW_PREAMBLE_in_preamble361); 
			PREAMBLE1_tree = (ScriptTree)adaptor.create(PREAMBLE1);
			adaptor.addChild(root_0, PREAMBLE1_tree);

			BEGIN2=(Token)match(input,BEGIN,FOLLOW_BEGIN_in_preamble363); 
			// edu/kit/iti/algover/script/Script.g:54:19: ( importDafny ';' !| importLibs ';' !| sets )+
			int cnt1=0;
			loop1:
			while (true) {
				int alt1=4;
				switch ( input.LA(1) ) {
				case IMPORT:
					{
					alt1=1;
					}
					break;
				case LIBRARY:
					{
					alt1=2;
					}
					break;
				case SETTINGS:
					{
					alt1=3;
					}
					break;
				}
				switch (alt1) {
				case 1 :
					// edu/kit/iti/algover/script/Script.g:54:21: importDafny ';' !
					{
					pushFollow(FOLLOW_importDafny_in_preamble368);
					importDafny3=importDafny();
					state._fsp--;

					adaptor.addChild(root_0, importDafny3.getTree());

					char_literal4=(Token)match(input,35,FOLLOW_35_in_preamble370); 
					}
					break;
				case 2 :
					// edu/kit/iti/algover/script/Script.g:54:41: importLibs ';' !
					{
					pushFollow(FOLLOW_importLibs_in_preamble376);
					importLibs5=importLibs();
					state._fsp--;

					adaptor.addChild(root_0, importLibs5.getTree());

					char_literal6=(Token)match(input,35,FOLLOW_35_in_preamble378); 
					}
					break;
				case 3 :
					// edu/kit/iti/algover/script/Script.g:54:59: sets
					{
					pushFollow(FOLLOW_sets_in_preamble383);
					sets7=sets();
					state._fsp--;

					adaptor.addChild(root_0, sets7.getTree());

					}
					break;

				default :
					if ( cnt1 >= 1 ) break loop1;
					EarlyExitException eee = new EarlyExitException(1, input);
					throw eee;
				}
				cnt1++;
			}

			END8=(Token)match(input,END,FOLLOW_END_in_preamble388); 
			// edu/kit/iti/algover/script/Script.g:54:72: ( pvcscripts )*
			loop2:
			while (true) {
				int alt2=2;
				int LA2_0 = input.LA(1);
				if ( (LA2_0==SUBSCRIPT) ) {
					alt2=1;
				}

				switch (alt2) {
				case 1 :
					// edu/kit/iti/algover/script/Script.g:54:72: pvcscripts
					{
					pushFollow(FOLLOW_pvcscripts_in_preamble391);
					pvcscripts9=pvcscripts();
					state._fsp--;

					adaptor.addChild(root_0, pvcscripts9.getTree());

					}
					break;

				default :
					break loop2;
				}
			}

			EOF10=(Token)match(input,EOF,FOLLOW_EOF_in_preamble394); 
			EOF10_tree = (ScriptTree)adaptor.create(EOF10);
			adaptor.addChild(root_0, EOF10_tree);

			}

			retval.stop = input.LT(-1);

			retval.tree = (ScriptTree)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
			retval.tree = (ScriptTree)adaptor.errorNode(input, retval.start, input.LT(-1), re);
		}
		finally {
			// do for sure before leaving
		}
		return retval;
	}
	// $ANTLR end "preamble"


	public static class importDafny_return extends ParserRuleReturnScope {
		ScriptTree tree;
		@Override
		public ScriptTree getTree() { return tree; }
	};


	// $ANTLR start "importDafny"
	// edu/kit/iti/algover/script/Script.g:57:1: importDafny : IMPORT ^ dafnyfiles ;
	public final ScriptParser.importDafny_return importDafny() throws RecognitionException {
		ScriptParser.importDafny_return retval = new ScriptParser.importDafny_return();
		retval.start = input.LT(1);

		ScriptTree root_0 = null;

		Token IMPORT11=null;
		ParserRuleReturnScope dafnyfiles12 =null;

		ScriptTree IMPORT11_tree=null;

		try {
			// edu/kit/iti/algover/script/Script.g:57:12: ( IMPORT ^ dafnyfiles )
			// edu/kit/iti/algover/script/Script.g:58:3: IMPORT ^ dafnyfiles
			{
			root_0 = (ScriptTree)adaptor.nil();


			IMPORT11=(Token)match(input,IMPORT,FOLLOW_IMPORT_in_importDafny406); 
			IMPORT11_tree = (ScriptTree)adaptor.create(IMPORT11);
			root_0 = (ScriptTree)adaptor.becomeRoot(IMPORT11_tree, root_0);

			pushFollow(FOLLOW_dafnyfiles_in_importDafny409);
			dafnyfiles12=dafnyfiles();
			state._fsp--;

			adaptor.addChild(root_0, dafnyfiles12.getTree());

			}

			retval.stop = input.LT(-1);

			retval.tree = (ScriptTree)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
			retval.tree = (ScriptTree)adaptor.errorNode(input, retval.start, input.LT(-1), re);
		}
		finally {
			// do for sure before leaving
		}
		return retval;
	}
	// $ANTLR end "importDafny"


	public static class importLibs_return extends ParserRuleReturnScope {
		ScriptTree tree;
		@Override
		public ScriptTree getTree() { return tree; }
	};


	// $ANTLR start "importLibs"
	// edu/kit/iti/algover/script/Script.g:61:1: importLibs : LIBRARY ^ dafnyfiles ;
	public final ScriptParser.importLibs_return importLibs() throws RecognitionException {
		ScriptParser.importLibs_return retval = new ScriptParser.importLibs_return();
		retval.start = input.LT(1);

		ScriptTree root_0 = null;

		Token LIBRARY13=null;
		ParserRuleReturnScope dafnyfiles14 =null;

		ScriptTree LIBRARY13_tree=null;

		try {
			// edu/kit/iti/algover/script/Script.g:61:11: ( LIBRARY ^ dafnyfiles )
			// edu/kit/iti/algover/script/Script.g:62:3: LIBRARY ^ dafnyfiles
			{
			root_0 = (ScriptTree)adaptor.nil();


			LIBRARY13=(Token)match(input,LIBRARY,FOLLOW_LIBRARY_in_importLibs421); 
			LIBRARY13_tree = (ScriptTree)adaptor.create(LIBRARY13);
			root_0 = (ScriptTree)adaptor.becomeRoot(LIBRARY13_tree, root_0);

			pushFollow(FOLLOW_dafnyfiles_in_importLibs424);
			dafnyfiles14=dafnyfiles();
			state._fsp--;

			adaptor.addChild(root_0, dafnyfiles14.getTree());

			}

			retval.stop = input.LT(-1);

			retval.tree = (ScriptTree)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
			retval.tree = (ScriptTree)adaptor.errorNode(input, retval.start, input.LT(-1), re);
		}
		finally {
			// do for sure before leaving
		}
		return retval;
	}
	// $ANTLR end "importLibs"


	public static class dafnyfiles_return extends ParserRuleReturnScope {
		ScriptTree tree;
		@Override
		public ScriptTree getTree() { return tree; }
	};


	// $ANTLR start "dafnyfiles"
	// edu/kit/iti/algover/script/Script.g:65:1: dafnyfiles : dafnyfile ( ',' ! dafnyfiles )* ;
	public final ScriptParser.dafnyfiles_return dafnyfiles() throws RecognitionException {
		ScriptParser.dafnyfiles_return retval = new ScriptParser.dafnyfiles_return();
		retval.start = input.LT(1);

		ScriptTree root_0 = null;

		Token char_literal16=null;
		ParserRuleReturnScope dafnyfile15 =null;
		ParserRuleReturnScope dafnyfiles17 =null;

		ScriptTree char_literal16_tree=null;

		try {
			// edu/kit/iti/algover/script/Script.g:65:11: ( dafnyfile ( ',' ! dafnyfiles )* )
			// edu/kit/iti/algover/script/Script.g:66:3: dafnyfile ( ',' ! dafnyfiles )*
			{
			root_0 = (ScriptTree)adaptor.nil();


			pushFollow(FOLLOW_dafnyfile_in_dafnyfiles436);
			dafnyfile15=dafnyfile();
			state._fsp--;

			adaptor.addChild(root_0, dafnyfile15.getTree());

			// edu/kit/iti/algover/script/Script.g:66:13: ( ',' ! dafnyfiles )*
			loop3:
			while (true) {
				int alt3=2;
				int LA3_0 = input.LA(1);
				if ( (LA3_0==33) ) {
					alt3=1;
				}

				switch (alt3) {
				case 1 :
					// edu/kit/iti/algover/script/Script.g:66:14: ',' ! dafnyfiles
					{
					char_literal16=(Token)match(input,33,FOLLOW_33_in_dafnyfiles439); 
					pushFollow(FOLLOW_dafnyfiles_in_dafnyfiles442);
					dafnyfiles17=dafnyfiles();
					state._fsp--;

					adaptor.addChild(root_0, dafnyfiles17.getTree());

					}
					break;

				default :
					break loop3;
				}
			}

			}

			retval.stop = input.LT(-1);

			retval.tree = (ScriptTree)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
			retval.tree = (ScriptTree)adaptor.errorNode(input, retval.start, input.LT(-1), re);
		}
		finally {
			// do for sure before leaving
		}
		return retval;
	}
	// $ANTLR end "dafnyfiles"


	public static class file_return extends ParserRuleReturnScope {
		ScriptTree tree;
		@Override
		public ScriptTree getTree() { return tree; }
	};


	// $ANTLR start "file"
	// edu/kit/iti/algover/script/Script.g:71:1: file : ( PATHSEP )* ( ID )+ ( ID | INT | PATHSEP )* ;
	public final ScriptParser.file_return file() throws RecognitionException {
		ScriptParser.file_return retval = new ScriptParser.file_return();
		retval.start = input.LT(1);

		ScriptTree root_0 = null;

		Token PATHSEP18=null;
		Token ID19=null;
		Token set20=null;

		ScriptTree PATHSEP18_tree=null;
		ScriptTree ID19_tree=null;
		ScriptTree set20_tree=null;

		try {
			// edu/kit/iti/algover/script/Script.g:71:5: ( ( PATHSEP )* ( ID )+ ( ID | INT | PATHSEP )* )
			// edu/kit/iti/algover/script/Script.g:72:3: ( PATHSEP )* ( ID )+ ( ID | INT | PATHSEP )*
			{
			root_0 = (ScriptTree)adaptor.nil();


			// edu/kit/iti/algover/script/Script.g:72:3: ( PATHSEP )*
			loop4:
			while (true) {
				int alt4=2;
				int LA4_0 = input.LA(1);
				if ( (LA4_0==PATHSEP) ) {
					alt4=1;
				}

				switch (alt4) {
				case 1 :
					// edu/kit/iti/algover/script/Script.g:72:4: PATHSEP
					{
					PATHSEP18=(Token)match(input,PATHSEP,FOLLOW_PATHSEP_in_file459); 
					PATHSEP18_tree = (ScriptTree)adaptor.create(PATHSEP18);
					adaptor.addChild(root_0, PATHSEP18_tree);

					}
					break;

				default :
					break loop4;
				}
			}

			// edu/kit/iti/algover/script/Script.g:72:13: ( ID )+
			int cnt5=0;
			loop5:
			while (true) {
				int alt5=2;
				int LA5_0 = input.LA(1);
				if ( (LA5_0==ID) ) {
					alt5=1;
				}

				switch (alt5) {
				case 1 :
					// edu/kit/iti/algover/script/Script.g:72:13: ID
					{
					ID19=(Token)match(input,ID,FOLLOW_ID_in_file462); 
					ID19_tree = (ScriptTree)adaptor.create(ID19);
					adaptor.addChild(root_0, ID19_tree);

					}
					break;

				default :
					if ( cnt5 >= 1 ) break loop5;
					EarlyExitException eee = new EarlyExitException(5, input);
					throw eee;
				}
				cnt5++;
			}

			// edu/kit/iti/algover/script/Script.g:72:16: ( ID | INT | PATHSEP )*
			loop6:
			while (true) {
				int alt6=2;
				int LA6_0 = input.LA(1);
				if ( (LA6_0==ID||LA6_0==INT||LA6_0==PATHSEP) ) {
					alt6=1;
				}

				switch (alt6) {
				case 1 :
					// edu/kit/iti/algover/script/Script.g:
					{
					set20=input.LT(1);
					if ( input.LA(1)==ID||input.LA(1)==INT||input.LA(1)==PATHSEP ) {
						input.consume();
						adaptor.addChild(root_0, (ScriptTree)adaptor.create(set20));
						state.errorRecovery=false;
					}
					else {
						MismatchedSetException mse = new MismatchedSetException(null,input);
						throw mse;
					}
					}
					break;

				default :
					break loop6;
				}
			}

			}

			retval.stop = input.LT(-1);

			retval.tree = (ScriptTree)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
			retval.tree = (ScriptTree)adaptor.errorNode(input, retval.start, input.LT(-1), re);
		}
		finally {
			// do for sure before leaving
		}
		return retval;
	}
	// $ANTLR end "file"


	public static class dafnyfile_return extends ParserRuleReturnScope {
		ScriptTree tree;
		@Override
		public ScriptTree getTree() { return tree; }
	};


	// $ANTLR start "dafnyfile"
	// edu/kit/iti/algover/script/Script.g:75:1: dafnyfile : file DAFNYEND -> ^( FILE file DAFNYEND ) ;
	public final ScriptParser.dafnyfile_return dafnyfile() throws RecognitionException {
		ScriptParser.dafnyfile_return retval = new ScriptParser.dafnyfile_return();
		retval.start = input.LT(1);

		ScriptTree root_0 = null;

		Token DAFNYEND22=null;
		ParserRuleReturnScope file21 =null;

		ScriptTree DAFNYEND22_tree=null;
		RewriteRuleTokenStream stream_DAFNYEND=new RewriteRuleTokenStream(adaptor,"token DAFNYEND");
		RewriteRuleSubtreeStream stream_file=new RewriteRuleSubtreeStream(adaptor,"rule file");

		try {
			// edu/kit/iti/algover/script/Script.g:75:10: ( file DAFNYEND -> ^( FILE file DAFNYEND ) )
			// edu/kit/iti/algover/script/Script.g:76:3: file DAFNYEND
			{
			pushFollow(FOLLOW_file_in_dafnyfile484);
			file21=file();
			state._fsp--;

			stream_file.add(file21.getTree());
			DAFNYEND22=(Token)match(input,DAFNYEND,FOLLOW_DAFNYEND_in_dafnyfile486);  
			stream_DAFNYEND.add(DAFNYEND22);

			// AST REWRITE
			// elements: file, DAFNYEND
			// token labels: 
			// rule labels: retval
			// token list labels: 
			// rule list labels: 
			// wildcard labels: 
			retval.tree = root_0;
			RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

			root_0 = (ScriptTree)adaptor.nil();
			// 77:5: -> ^( FILE file DAFNYEND )
			{
				// edu/kit/iti/algover/script/Script.g:77:8: ^( FILE file DAFNYEND )
				{
				ScriptTree root_1 = (ScriptTree)adaptor.nil();
				root_1 = (ScriptTree)adaptor.becomeRoot((ScriptTree)adaptor.create(FILE, "FILE"), root_1);
				adaptor.addChild(root_1, stream_file.nextTree());
				adaptor.addChild(root_1, stream_DAFNYEND.nextNode());
				adaptor.addChild(root_0, root_1);
				}

			}


			retval.tree = root_0;

			}

			retval.stop = input.LT(-1);

			retval.tree = (ScriptTree)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
			retval.tree = (ScriptTree)adaptor.errorNode(input, retval.start, input.LT(-1), re);
		}
		finally {
			// do for sure before leaving
		}
		return retval;
	}
	// $ANTLR end "dafnyfile"


	public static class sets_return extends ParserRuleReturnScope {
		ScriptTree tree;
		@Override
		public ScriptTree getTree() { return tree; }
	};


	// $ANTLR start "sets"
	// edu/kit/iti/algover/script/Script.g:80:1: sets : SETTINGS ^ set ( set )* ;
	public final ScriptParser.sets_return sets() throws RecognitionException {
		ScriptParser.sets_return retval = new ScriptParser.sets_return();
		retval.start = input.LT(1);

		ScriptTree root_0 = null;

		Token SETTINGS23=null;
		ParserRuleReturnScope set24 =null;
		ParserRuleReturnScope set25 =null;

		ScriptTree SETTINGS23_tree=null;

		try {
			// edu/kit/iti/algover/script/Script.g:80:5: ( SETTINGS ^ set ( set )* )
			// edu/kit/iti/algover/script/Script.g:81:3: SETTINGS ^ set ( set )*
			{
			root_0 = (ScriptTree)adaptor.nil();


			SETTINGS23=(Token)match(input,SETTINGS,FOLLOW_SETTINGS_in_sets512); 
			SETTINGS23_tree = (ScriptTree)adaptor.create(SETTINGS23);
			root_0 = (ScriptTree)adaptor.becomeRoot(SETTINGS23_tree, root_0);

			pushFollow(FOLLOW_set_in_sets515);
			set24=set();
			state._fsp--;

			adaptor.addChild(root_0, set24.getTree());

			// edu/kit/iti/algover/script/Script.g:81:17: ( set )*
			loop7:
			while (true) {
				int alt7=2;
				int LA7_0 = input.LA(1);
				if ( (LA7_0==37) ) {
					alt7=1;
				}

				switch (alt7) {
				case 1 :
					// edu/kit/iti/algover/script/Script.g:81:18: set
					{
					pushFollow(FOLLOW_set_in_sets518);
					set25=set();
					state._fsp--;

					adaptor.addChild(root_0, set25.getTree());

					}
					break;

				default :
					break loop7;
				}
			}

			}

			retval.stop = input.LT(-1);

			retval.tree = (ScriptTree)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
			retval.tree = (ScriptTree)adaptor.errorNode(input, retval.start, input.LT(-1), re);
		}
		finally {
			// do for sure before leaving
		}
		return retval;
	}
	// $ANTLR end "sets"


	public static class set_return extends ParserRuleReturnScope {
		ScriptTree tree;
		@Override
		public ScriptTree getTree() { return tree; }
	};


	// $ANTLR start "set"
	// edu/kit/iti/algover/script/Script.g:84:1: set : '[' (tok= ( DAFNYTIMEOUT | KEYTIMEOUT ) ) ']' ( INT )+ ';' -> ^( SET[tok] ( INT )+ ) ;
	public final ScriptParser.set_return set() throws RecognitionException {
		ScriptParser.set_return retval = new ScriptParser.set_return();
		retval.start = input.LT(1);

		ScriptTree root_0 = null;

		Token tok=null;
		Token char_literal26=null;
		Token char_literal27=null;
		Token INT28=null;
		Token char_literal29=null;

		ScriptTree tok_tree=null;
		ScriptTree char_literal26_tree=null;
		ScriptTree char_literal27_tree=null;
		ScriptTree INT28_tree=null;
		ScriptTree char_literal29_tree=null;
		RewriteRuleTokenStream stream_35=new RewriteRuleTokenStream(adaptor,"token 35");
		RewriteRuleTokenStream stream_37=new RewriteRuleTokenStream(adaptor,"token 37");
		RewriteRuleTokenStream stream_38=new RewriteRuleTokenStream(adaptor,"token 38");
		RewriteRuleTokenStream stream_KEYTIMEOUT=new RewriteRuleTokenStream(adaptor,"token KEYTIMEOUT");
		RewriteRuleTokenStream stream_DAFNYTIMEOUT=new RewriteRuleTokenStream(adaptor,"token DAFNYTIMEOUT");
		RewriteRuleTokenStream stream_INT=new RewriteRuleTokenStream(adaptor,"token INT");

		try {
			// edu/kit/iti/algover/script/Script.g:84:4: ( '[' (tok= ( DAFNYTIMEOUT | KEYTIMEOUT ) ) ']' ( INT )+ ';' -> ^( SET[tok] ( INT )+ ) )
			// edu/kit/iti/algover/script/Script.g:85:3: '[' (tok= ( DAFNYTIMEOUT | KEYTIMEOUT ) ) ']' ( INT )+ ';'
			{
			char_literal26=(Token)match(input,37,FOLLOW_37_in_set530);  
			stream_37.add(char_literal26);

			// edu/kit/iti/algover/script/Script.g:85:7: (tok= ( DAFNYTIMEOUT | KEYTIMEOUT ) )
			// edu/kit/iti/algover/script/Script.g:85:8: tok= ( DAFNYTIMEOUT | KEYTIMEOUT )
			{
			// edu/kit/iti/algover/script/Script.g:85:12: ( DAFNYTIMEOUT | KEYTIMEOUT )
			int alt8=2;
			int LA8_0 = input.LA(1);
			if ( (LA8_0==DAFNYTIMEOUT) ) {
				alt8=1;
			}
			else if ( (LA8_0==KEYTIMEOUT) ) {
				alt8=2;
			}

			else {
				NoViableAltException nvae =
					new NoViableAltException("", 8, 0, input);
				throw nvae;
			}

			switch (alt8) {
				case 1 :
					// edu/kit/iti/algover/script/Script.g:85:13: DAFNYTIMEOUT
					{
					tok=(Token)match(input,DAFNYTIMEOUT,FOLLOW_DAFNYTIMEOUT_in_set536);  
					stream_DAFNYTIMEOUT.add(tok);

					}
					break;
				case 2 :
					// edu/kit/iti/algover/script/Script.g:85:26: KEYTIMEOUT
					{
					tok=(Token)match(input,KEYTIMEOUT,FOLLOW_KEYTIMEOUT_in_set538);  
					stream_KEYTIMEOUT.add(tok);

					}
					break;

			}

			}

			char_literal27=(Token)match(input,38,FOLLOW_38_in_set542);  
			stream_38.add(char_literal27);

			// edu/kit/iti/algover/script/Script.g:85:43: ( INT )+
			int cnt9=0;
			loop9:
			while (true) {
				int alt9=2;
				int LA9_0 = input.LA(1);
				if ( (LA9_0==INT) ) {
					alt9=1;
				}

				switch (alt9) {
				case 1 :
					// edu/kit/iti/algover/script/Script.g:85:43: INT
					{
					INT28=(Token)match(input,INT,FOLLOW_INT_in_set544);  
					stream_INT.add(INT28);

					}
					break;

				default :
					if ( cnt9 >= 1 ) break loop9;
					EarlyExitException eee = new EarlyExitException(9, input);
					throw eee;
				}
				cnt9++;
			}

			char_literal29=(Token)match(input,35,FOLLOW_35_in_set547);  
			stream_35.add(char_literal29);

			// AST REWRITE
			// elements: INT
			// token labels: 
			// rule labels: retval
			// token list labels: 
			// rule list labels: 
			// wildcard labels: 
			retval.tree = root_0;
			RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

			root_0 = (ScriptTree)adaptor.nil();
			// 86:5: -> ^( SET[tok] ( INT )+ )
			{
				// edu/kit/iti/algover/script/Script.g:86:8: ^( SET[tok] ( INT )+ )
				{
				ScriptTree root_1 = (ScriptTree)adaptor.nil();
				root_1 = (ScriptTree)adaptor.becomeRoot((ScriptTree)adaptor.create(SET, tok), root_1);
				if ( !(stream_INT.hasNext()) ) {
					throw new RewriteEarlyExitException();
				}
				while ( stream_INT.hasNext() ) {
					adaptor.addChild(root_1, stream_INT.nextNode());
				}
				stream_INT.reset();

				adaptor.addChild(root_0, root_1);
				}

			}


			retval.tree = root_0;

			}

			retval.stop = input.LT(-1);

			retval.tree = (ScriptTree)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
			retval.tree = (ScriptTree)adaptor.errorNode(input, retval.start, input.LT(-1), re);
		}
		finally {
			// do for sure before leaving
		}
		return retval;
	}
	// $ANTLR end "set"


	public static class pvcscripts_return extends ParserRuleReturnScope {
		ScriptTree tree;
		@Override
		public ScriptTree getTree() { return tree; }
	};


	// $ANTLR start "pvcscripts"
	// edu/kit/iti/algover/script/Script.g:89:1: pvcscripts : pvcscript ( pvcscripts )* ;
	public final ScriptParser.pvcscripts_return pvcscripts() throws RecognitionException {
		ScriptParser.pvcscripts_return retval = new ScriptParser.pvcscripts_return();
		retval.start = input.LT(1);

		ScriptTree root_0 = null;

		ParserRuleReturnScope pvcscript30 =null;
		ParserRuleReturnScope pvcscripts31 =null;


		try {
			// edu/kit/iti/algover/script/Script.g:89:11: ( pvcscript ( pvcscripts )* )
			// edu/kit/iti/algover/script/Script.g:90:3: pvcscript ( pvcscripts )*
			{
			root_0 = (ScriptTree)adaptor.nil();


			pushFollow(FOLLOW_pvcscript_in_pvcscripts574);
			pvcscript30=pvcscript();
			state._fsp--;

			adaptor.addChild(root_0, pvcscript30.getTree());

			// edu/kit/iti/algover/script/Script.g:90:13: ( pvcscripts )*
			loop10:
			while (true) {
				int alt10=2;
				int LA10_0 = input.LA(1);
				if ( (LA10_0==SUBSCRIPT) ) {
					alt10=1;
				}

				switch (alt10) {
				case 1 :
					// edu/kit/iti/algover/script/Script.g:90:14: pvcscripts
					{
					pushFollow(FOLLOW_pvcscripts_in_pvcscripts577);
					pvcscripts31=pvcscripts();
					state._fsp--;

					adaptor.addChild(root_0, pvcscripts31.getTree());

					}
					break;

				default :
					break loop10;
				}
			}

			}

			retval.stop = input.LT(-1);

			retval.tree = (ScriptTree)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
			retval.tree = (ScriptTree)adaptor.errorNode(input, retval.start, input.LT(-1), re);
		}
		finally {
			// do for sure before leaving
		}
		return retval;
	}
	// $ANTLR end "pvcscripts"


	public static class pvcscript_return extends ParserRuleReturnScope {
		ScriptTree tree;
		@Override
		public ScriptTree getTree() { return tree; }
	};


	// $ANTLR start "pvcscript"
	// edu/kit/iti/algover/script/Script.g:93:1: pvcscript : SUBSCRIPT ^ pvc ':' '{' ( commands )* ( QED )? '}' ;
	public final ScriptParser.pvcscript_return pvcscript() throws RecognitionException {
		ScriptParser.pvcscript_return retval = new ScriptParser.pvcscript_return();
		retval.start = input.LT(1);

		ScriptTree root_0 = null;

		Token SUBSCRIPT32=null;
		Token char_literal34=null;
		Token char_literal35=null;
		Token QED37=null;
		Token char_literal38=null;
		ParserRuleReturnScope pvc33 =null;
		ParserRuleReturnScope commands36 =null;

		ScriptTree SUBSCRIPT32_tree=null;
		ScriptTree char_literal34_tree=null;
		ScriptTree char_literal35_tree=null;
		ScriptTree QED37_tree=null;
		ScriptTree char_literal38_tree=null;

		try {
			// edu/kit/iti/algover/script/Script.g:93:10: ( SUBSCRIPT ^ pvc ':' '{' ( commands )* ( QED )? '}' )
			// edu/kit/iti/algover/script/Script.g:94:3: SUBSCRIPT ^ pvc ':' '{' ( commands )* ( QED )? '}'
			{
			root_0 = (ScriptTree)adaptor.nil();


			SUBSCRIPT32=(Token)match(input,SUBSCRIPT,FOLLOW_SUBSCRIPT_in_pvcscript591); 
			SUBSCRIPT32_tree = (ScriptTree)adaptor.create(SUBSCRIPT32);
			root_0 = (ScriptTree)adaptor.becomeRoot(SUBSCRIPT32_tree, root_0);

			pushFollow(FOLLOW_pvc_in_pvcscript594);
			pvc33=pvc();
			state._fsp--;

			adaptor.addChild(root_0, pvc33.getTree());

			char_literal34=(Token)match(input,34,FOLLOW_34_in_pvcscript596); 
			char_literal34_tree = (ScriptTree)adaptor.create(char_literal34);
			adaptor.addChild(root_0, char_literal34_tree);

			char_literal35=(Token)match(input,39,FOLLOW_39_in_pvcscript598); 
			char_literal35_tree = (ScriptTree)adaptor.create(char_literal35);
			adaptor.addChild(root_0, char_literal35_tree);

			// edu/kit/iti/algover/script/Script.g:94:26: ( commands )*
			loop11:
			while (true) {
				int alt11=2;
				int LA11_0 = input.LA(1);
				if ( (LA11_0==ID) ) {
					alt11=1;
				}

				switch (alt11) {
				case 1 :
					// edu/kit/iti/algover/script/Script.g:94:26: commands
					{
					pushFollow(FOLLOW_commands_in_pvcscript600);
					commands36=commands();
					state._fsp--;

					adaptor.addChild(root_0, commands36.getTree());

					}
					break;

				default :
					break loop11;
				}
			}

			// edu/kit/iti/algover/script/Script.g:94:36: ( QED )?
			int alt12=2;
			int LA12_0 = input.LA(1);
			if ( (LA12_0==QED) ) {
				alt12=1;
			}
			switch (alt12) {
				case 1 :
					// edu/kit/iti/algover/script/Script.g:94:36: QED
					{
					QED37=(Token)match(input,QED,FOLLOW_QED_in_pvcscript603); 
					QED37_tree = (ScriptTree)adaptor.create(QED37);
					adaptor.addChild(root_0, QED37_tree);

					}
					break;

			}

			char_literal38=(Token)match(input,40,FOLLOW_40_in_pvcscript606); 
			char_literal38_tree = (ScriptTree)adaptor.create(char_literal38);
			adaptor.addChild(root_0, char_literal38_tree);

			}

			retval.stop = input.LT(-1);

			retval.tree = (ScriptTree)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
			retval.tree = (ScriptTree)adaptor.errorNode(input, retval.start, input.LT(-1), re);
		}
		finally {
			// do for sure before leaving
		}
		return retval;
	}
	// $ANTLR end "pvcscript"


	public static class pvc_return extends ParserRuleReturnScope {
		ScriptTree tree;
		@Override
		public ScriptTree getTree() { return tree; }
	};


	// $ANTLR start "pvc"
	// edu/kit/iti/algover/script/Script.g:97:1: pvc : 'PVC_' ( INT )+ ;
	public final ScriptParser.pvc_return pvc() throws RecognitionException {
		ScriptParser.pvc_return retval = new ScriptParser.pvc_return();
		retval.start = input.LT(1);

		ScriptTree root_0 = null;

		Token string_literal39=null;
		Token INT40=null;

		ScriptTree string_literal39_tree=null;
		ScriptTree INT40_tree=null;

		try {
			// edu/kit/iti/algover/script/Script.g:97:4: ( 'PVC_' ( INT )+ )
			// edu/kit/iti/algover/script/Script.g:98:3: 'PVC_' ( INT )+
			{
			root_0 = (ScriptTree)adaptor.nil();


			string_literal39=(Token)match(input,36,FOLLOW_36_in_pvc618); 
			string_literal39_tree = (ScriptTree)adaptor.create(string_literal39);
			adaptor.addChild(root_0, string_literal39_tree);

			// edu/kit/iti/algover/script/Script.g:98:10: ( INT )+
			int cnt13=0;
			loop13:
			while (true) {
				int alt13=2;
				int LA13_0 = input.LA(1);
				if ( (LA13_0==INT) ) {
					alt13=1;
				}

				switch (alt13) {
				case 1 :
					// edu/kit/iti/algover/script/Script.g:98:10: INT
					{
					INT40=(Token)match(input,INT,FOLLOW_INT_in_pvc620); 
					INT40_tree = (ScriptTree)adaptor.create(INT40);
					adaptor.addChild(root_0, INT40_tree);

					}
					break;

				default :
					if ( cnt13 >= 1 ) break loop13;
					EarlyExitException eee = new EarlyExitException(13, input);
					throw eee;
				}
				cnt13++;
			}

			}

			retval.stop = input.LT(-1);

			retval.tree = (ScriptTree)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
			retval.tree = (ScriptTree)adaptor.errorNode(input, retval.start, input.LT(-1), re);
		}
		finally {
			// do for sure before leaving
		}
		return retval;
	}
	// $ANTLR end "pvc"


	public static class branchingcommand_return extends ParserRuleReturnScope {
		ScriptTree tree;
		@Override
		public ScriptTree getTree() { return tree; }
	};


	// $ANTLR start "branchingcommand"
	// edu/kit/iti/algover/script/Script.g:101:1: branchingcommand : ( ID )+ ';' '{' ( commands )+ '}' '{' ( commands )+ '}' ;
	public final ScriptParser.branchingcommand_return branchingcommand() throws RecognitionException {
		ScriptParser.branchingcommand_return retval = new ScriptParser.branchingcommand_return();
		retval.start = input.LT(1);

		ScriptTree root_0 = null;

		Token ID41=null;
		Token char_literal42=null;
		Token char_literal43=null;
		Token char_literal45=null;
		Token char_literal46=null;
		Token char_literal48=null;
		ParserRuleReturnScope commands44 =null;
		ParserRuleReturnScope commands47 =null;

		ScriptTree ID41_tree=null;
		ScriptTree char_literal42_tree=null;
		ScriptTree char_literal43_tree=null;
		ScriptTree char_literal45_tree=null;
		ScriptTree char_literal46_tree=null;
		ScriptTree char_literal48_tree=null;

		try {
			// edu/kit/iti/algover/script/Script.g:101:17: ( ( ID )+ ';' '{' ( commands )+ '}' '{' ( commands )+ '}' )
			// edu/kit/iti/algover/script/Script.g:102:3: ( ID )+ ';' '{' ( commands )+ '}' '{' ( commands )+ '}'
			{
			root_0 = (ScriptTree)adaptor.nil();


			// edu/kit/iti/algover/script/Script.g:102:3: ( ID )+
			int cnt14=0;
			loop14:
			while (true) {
				int alt14=2;
				int LA14_0 = input.LA(1);
				if ( (LA14_0==ID) ) {
					alt14=1;
				}

				switch (alt14) {
				case 1 :
					// edu/kit/iti/algover/script/Script.g:102:3: ID
					{
					ID41=(Token)match(input,ID,FOLLOW_ID_in_branchingcommand633); 
					ID41_tree = (ScriptTree)adaptor.create(ID41);
					adaptor.addChild(root_0, ID41_tree);

					}
					break;

				default :
					if ( cnt14 >= 1 ) break loop14;
					EarlyExitException eee = new EarlyExitException(14, input);
					throw eee;
				}
				cnt14++;
			}

			char_literal42=(Token)match(input,35,FOLLOW_35_in_branchingcommand636); 
			char_literal42_tree = (ScriptTree)adaptor.create(char_literal42);
			adaptor.addChild(root_0, char_literal42_tree);

			char_literal43=(Token)match(input,39,FOLLOW_39_in_branchingcommand640); 
			char_literal43_tree = (ScriptTree)adaptor.create(char_literal43);
			adaptor.addChild(root_0, char_literal43_tree);

			// edu/kit/iti/algover/script/Script.g:103:7: ( commands )+
			int cnt15=0;
			loop15:
			while (true) {
				int alt15=2;
				int LA15_0 = input.LA(1);
				if ( (LA15_0==ID) ) {
					alt15=1;
				}

				switch (alt15) {
				case 1 :
					// edu/kit/iti/algover/script/Script.g:103:7: commands
					{
					pushFollow(FOLLOW_commands_in_branchingcommand642);
					commands44=commands();
					state._fsp--;

					adaptor.addChild(root_0, commands44.getTree());

					}
					break;

				default :
					if ( cnt15 >= 1 ) break loop15;
					EarlyExitException eee = new EarlyExitException(15, input);
					throw eee;
				}
				cnt15++;
			}

			char_literal45=(Token)match(input,40,FOLLOW_40_in_branchingcommand645); 
			char_literal45_tree = (ScriptTree)adaptor.create(char_literal45);
			adaptor.addChild(root_0, char_literal45_tree);

			char_literal46=(Token)match(input,39,FOLLOW_39_in_branchingcommand649); 
			char_literal46_tree = (ScriptTree)adaptor.create(char_literal46);
			adaptor.addChild(root_0, char_literal46_tree);

			// edu/kit/iti/algover/script/Script.g:104:7: ( commands )+
			int cnt16=0;
			loop16:
			while (true) {
				int alt16=2;
				int LA16_0 = input.LA(1);
				if ( (LA16_0==ID) ) {
					alt16=1;
				}

				switch (alt16) {
				case 1 :
					// edu/kit/iti/algover/script/Script.g:104:7: commands
					{
					pushFollow(FOLLOW_commands_in_branchingcommand651);
					commands47=commands();
					state._fsp--;

					adaptor.addChild(root_0, commands47.getTree());

					}
					break;

				default :
					if ( cnt16 >= 1 ) break loop16;
					EarlyExitException eee = new EarlyExitException(16, input);
					throw eee;
				}
				cnt16++;
			}

			char_literal48=(Token)match(input,40,FOLLOW_40_in_branchingcommand654); 
			char_literal48_tree = (ScriptTree)adaptor.create(char_literal48);
			adaptor.addChild(root_0, char_literal48_tree);

			}

			retval.stop = input.LT(-1);

			retval.tree = (ScriptTree)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
			retval.tree = (ScriptTree)adaptor.errorNode(input, retval.start, input.LT(-1), re);
		}
		finally {
			// do for sure before leaving
		}
		return retval;
	}
	// $ANTLR end "branchingcommand"


	public static class commands_return extends ParserRuleReturnScope {
		ScriptTree tree;
		@Override
		public ScriptTree getTree() { return tree; }
	};


	// $ANTLR start "commands"
	// edu/kit/iti/algover/script/Script.g:107:1: commands : ( command | branchingcommand );
	public final ScriptParser.commands_return commands() throws RecognitionException {
		ScriptParser.commands_return retval = new ScriptParser.commands_return();
		retval.start = input.LT(1);

		ScriptTree root_0 = null;

		ParserRuleReturnScope command49 =null;
		ParserRuleReturnScope branchingcommand50 =null;


		try {
			// edu/kit/iti/algover/script/Script.g:107:9: ( command | branchingcommand )
			int alt17=2;
			alt17 = dfa17.predict(input);
			switch (alt17) {
				case 1 :
					// edu/kit/iti/algover/script/Script.g:108:3: command
					{
					root_0 = (ScriptTree)adaptor.nil();


					pushFollow(FOLLOW_command_in_commands666);
					command49=command();
					state._fsp--;

					adaptor.addChild(root_0, command49.getTree());

					}
					break;
				case 2 :
					// edu/kit/iti/algover/script/Script.g:108:13: branchingcommand
					{
					root_0 = (ScriptTree)adaptor.nil();


					pushFollow(FOLLOW_branchingcommand_in_commands670);
					branchingcommand50=branchingcommand();
					state._fsp--;

					adaptor.addChild(root_0, branchingcommand50.getTree());

					}
					break;

			}
			retval.stop = input.LT(-1);

			retval.tree = (ScriptTree)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
			retval.tree = (ScriptTree)adaptor.errorNode(input, retval.start, input.LT(-1), re);
		}
		finally {
			// do for sure before leaving
		}
		return retval;
	}
	// $ANTLR end "commands"


	public static class command_return extends ParserRuleReturnScope {
		ScriptTree tree;
		@Override
		public ScriptTree getTree() { return tree; }
	};


	// $ANTLR start "command"
	// edu/kit/iti/algover/script/Script.g:111:1: command : ( ID )+ ';' ;
	public final ScriptParser.command_return command() throws RecognitionException {
		ScriptParser.command_return retval = new ScriptParser.command_return();
		retval.start = input.LT(1);

		ScriptTree root_0 = null;

		Token ID51=null;
		Token char_literal52=null;

		ScriptTree ID51_tree=null;
		ScriptTree char_literal52_tree=null;

		try {
			// edu/kit/iti/algover/script/Script.g:111:9: ( ( ID )+ ';' )
			// edu/kit/iti/algover/script/Script.g:112:3: ( ID )+ ';'
			{
			root_0 = (ScriptTree)adaptor.nil();


			// edu/kit/iti/algover/script/Script.g:112:3: ( ID )+
			int cnt18=0;
			loop18:
			while (true) {
				int alt18=2;
				int LA18_0 = input.LA(1);
				if ( (LA18_0==ID) ) {
					alt18=1;
				}

				switch (alt18) {
				case 1 :
					// edu/kit/iti/algover/script/Script.g:112:3: ID
					{
					ID51=(Token)match(input,ID,FOLLOW_ID_in_command683); 
					ID51_tree = (ScriptTree)adaptor.create(ID51);
					adaptor.addChild(root_0, ID51_tree);

					}
					break;

				default :
					if ( cnt18 >= 1 ) break loop18;
					EarlyExitException eee = new EarlyExitException(18, input);
					throw eee;
				}
				cnt18++;
			}

			char_literal52=(Token)match(input,35,FOLLOW_35_in_command686); 
			char_literal52_tree = (ScriptTree)adaptor.create(char_literal52);
			adaptor.addChild(root_0, char_literal52_tree);

			}

			retval.stop = input.LT(-1);

			retval.tree = (ScriptTree)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
			retval.tree = (ScriptTree)adaptor.errorNode(input, retval.start, input.LT(-1), re);
		}
		finally {
			// do for sure before leaving
		}
		return retval;
	}
	// $ANTLR end "command"

	// Delegated rules


	protected DFA17 dfa17 = new DFA17(this);
	static final String DFA17_eotS =
		"\5\uffff";
	static final String DFA17_eofS =
		"\5\uffff";
	static final String DFA17_minS =
		"\3\13\2\uffff";
	static final String DFA17_maxS =
		"\1\13\1\43\1\50\2\uffff";
	static final String DFA17_acceptS =
		"\3\uffff\1\2\1\1";
	static final String DFA17_specialS =
		"\5\uffff}>";
	static final String[] DFA17_transitionS = {
			"\1\1",
			"\1\1\27\uffff\1\2",
			"\1\4\14\uffff\1\4\16\uffff\1\3\1\4",
			"",
			""
	};

	static final short[] DFA17_eot = DFA.unpackEncodedString(DFA17_eotS);
	static final short[] DFA17_eof = DFA.unpackEncodedString(DFA17_eofS);
	static final char[] DFA17_min = DFA.unpackEncodedStringToUnsignedChars(DFA17_minS);
	static final char[] DFA17_max = DFA.unpackEncodedStringToUnsignedChars(DFA17_maxS);
	static final short[] DFA17_accept = DFA.unpackEncodedString(DFA17_acceptS);
	static final short[] DFA17_special = DFA.unpackEncodedString(DFA17_specialS);
	static final short[][] DFA17_transition;

	static {
		int numStates = DFA17_transitionS.length;
		DFA17_transition = new short[numStates][];
		for (int i=0; i<numStates; i++) {
			DFA17_transition[i] = DFA.unpackEncodedString(DFA17_transitionS[i]);
		}
	}

	protected class DFA17 extends DFA {

		public DFA17(BaseRecognizer recognizer) {
			this.recognizer = recognizer;
			this.decisionNumber = 17;
			this.eot = DFA17_eot;
			this.eof = DFA17_eof;
			this.min = DFA17_min;
			this.max = DFA17_max;
			this.accept = DFA17_accept;
			this.special = DFA17_special;
			this.transition = DFA17_transition;
		}
		@Override
		public String getDescription() {
			return "107:1: commands : ( command | branchingcommand );";
		}
	}

	public static final BitSet FOLLOW_PREAMBLE_in_preamble361 = new BitSet(new long[]{0x0000000000000020L});
	public static final BitSet FOLLOW_BEGIN_in_preamble363 = new BitSet(new long[]{0x0000000004011000L});
	public static final BitSet FOLLOW_importDafny_in_preamble368 = new BitSet(new long[]{0x0000000800000000L});
	public static final BitSet FOLLOW_35_in_preamble370 = new BitSet(new long[]{0x0000000004011100L});
	public static final BitSet FOLLOW_importLibs_in_preamble376 = new BitSet(new long[]{0x0000000800000000L});
	public static final BitSet FOLLOW_35_in_preamble378 = new BitSet(new long[]{0x0000000004011100L});
	public static final BitSet FOLLOW_sets_in_preamble383 = new BitSet(new long[]{0x0000000004011100L});
	public static final BitSet FOLLOW_END_in_preamble388 = new BitSet(new long[]{0x0000000010000000L});
	public static final BitSet FOLLOW_pvcscripts_in_preamble391 = new BitSet(new long[]{0x0000000010000000L});
	public static final BitSet FOLLOW_EOF_in_preamble394 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_IMPORT_in_importDafny406 = new BitSet(new long[]{0x0000000000080800L});
	public static final BitSet FOLLOW_dafnyfiles_in_importDafny409 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_LIBRARY_in_importLibs421 = new BitSet(new long[]{0x0000000000080800L});
	public static final BitSet FOLLOW_dafnyfiles_in_importLibs424 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_dafnyfile_in_dafnyfiles436 = new BitSet(new long[]{0x0000000200000002L});
	public static final BitSet FOLLOW_33_in_dafnyfiles439 = new BitSet(new long[]{0x0000000000080800L});
	public static final BitSet FOLLOW_dafnyfiles_in_dafnyfiles442 = new BitSet(new long[]{0x0000000200000002L});
	public static final BitSet FOLLOW_PATHSEP_in_file459 = new BitSet(new long[]{0x0000000000080800L});
	public static final BitSet FOLLOW_ID_in_file462 = new BitSet(new long[]{0x0000000000084802L});
	public static final BitSet FOLLOW_file_in_dafnyfile484 = new BitSet(new long[]{0x0000000000000040L});
	public static final BitSet FOLLOW_DAFNYEND_in_dafnyfile486 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_SETTINGS_in_sets512 = new BitSet(new long[]{0x0000002000000000L});
	public static final BitSet FOLLOW_set_in_sets515 = new BitSet(new long[]{0x0000002000000002L});
	public static final BitSet FOLLOW_set_in_sets518 = new BitSet(new long[]{0x0000002000000002L});
	public static final BitSet FOLLOW_37_in_set530 = new BitSet(new long[]{0x0000000000008080L});
	public static final BitSet FOLLOW_DAFNYTIMEOUT_in_set536 = new BitSet(new long[]{0x0000004000000000L});
	public static final BitSet FOLLOW_KEYTIMEOUT_in_set538 = new BitSet(new long[]{0x0000004000000000L});
	public static final BitSet FOLLOW_38_in_set542 = new BitSet(new long[]{0x0000000000004000L});
	public static final BitSet FOLLOW_INT_in_set544 = new BitSet(new long[]{0x0000000800004000L});
	public static final BitSet FOLLOW_35_in_set547 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_pvcscript_in_pvcscripts574 = new BitSet(new long[]{0x0000000010000002L});
	public static final BitSet FOLLOW_pvcscripts_in_pvcscripts577 = new BitSet(new long[]{0x0000000010000002L});
	public static final BitSet FOLLOW_SUBSCRIPT_in_pvcscript591 = new BitSet(new long[]{0x0000001000000000L});
	public static final BitSet FOLLOW_pvc_in_pvcscript594 = new BitSet(new long[]{0x0000000400000000L});
	public static final BitSet FOLLOW_34_in_pvcscript596 = new BitSet(new long[]{0x0000008000000000L});
	public static final BitSet FOLLOW_39_in_pvcscript598 = new BitSet(new long[]{0x0000010001000800L});
	public static final BitSet FOLLOW_commands_in_pvcscript600 = new BitSet(new long[]{0x0000010001000800L});
	public static final BitSet FOLLOW_QED_in_pvcscript603 = new BitSet(new long[]{0x0000010000000000L});
	public static final BitSet FOLLOW_40_in_pvcscript606 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_36_in_pvc618 = new BitSet(new long[]{0x0000000000004000L});
	public static final BitSet FOLLOW_INT_in_pvc620 = new BitSet(new long[]{0x0000000000004002L});
	public static final BitSet FOLLOW_ID_in_branchingcommand633 = new BitSet(new long[]{0x0000000800000800L});
	public static final BitSet FOLLOW_35_in_branchingcommand636 = new BitSet(new long[]{0x0000008000000000L});
	public static final BitSet FOLLOW_39_in_branchingcommand640 = new BitSet(new long[]{0x0000000000000800L});
	public static final BitSet FOLLOW_commands_in_branchingcommand642 = new BitSet(new long[]{0x0000010000000800L});
	public static final BitSet FOLLOW_40_in_branchingcommand645 = new BitSet(new long[]{0x0000008000000000L});
	public static final BitSet FOLLOW_39_in_branchingcommand649 = new BitSet(new long[]{0x0000000000000800L});
	public static final BitSet FOLLOW_commands_in_branchingcommand651 = new BitSet(new long[]{0x0000010000000800L});
	public static final BitSet FOLLOW_40_in_branchingcommand654 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_command_in_commands666 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_branchingcommand_in_commands670 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_ID_in_command683 = new BitSet(new long[]{0x0000000800000800L});
	public static final BitSet FOLLOW_35_in_command686 = new BitSet(new long[]{0x0000000000000002L});
}
