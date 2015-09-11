// $ANTLR 3.5.1 Dafny.g 2015-09-11 12:18:35

  package edu.kit.iti.algover.parser;


import org.antlr.runtime.*;
import java.util.Stack;
import java.util.List;
import java.util.ArrayList;
import java.util.Map;
import java.util.HashMap;

import org.antlr.runtime.tree.*;


@SuppressWarnings("all")
public class DafnyParser extends Parser {
	public static final String[] tokenNames = new String[] {
		"<invalid>", "<EOR>", "<DOWN>", "<UP>", "ALL", "AND", "ARGS", "ARRAY", 
		"ARRAY_ACCESS", "ASSERT", "ASSIGN", "BLOCK", "BLOCK_BEGIN", "BLOCK_END", 
		"CALL", "DECREASES", "DOT", "DOUBLECOLON", "ELSE", "ENSURES", "EQ", "EX", 
		"GE", "GT", "ID", "IF", "IMPLIES", "INT", "INTERSECT", "INVARIANT", "LABEL", 
		"LE", "LEMMA", "LENGTH", "LISTEX", "LIT", "LT", "METHOD", "MINUS", "NOT", 
		"OR", "PLUS", "REQUIRES", "RESULTS", "RETURNS", "SET", "SETEX", "THEN", 
		"TIMES", "UNION", "VAR", "WHILE", "WS", "'('", "')'", "','", "':'", "';'", 
		"'['", "']'"
	};
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
	public Parser[] getDelegates() {
		return new Parser[] {};
	}

	// delegators


	public DafnyParser(TokenStream input) {
		this(input, new RecognizerSharedState());
	}
	public DafnyParser(TokenStream input, RecognizerSharedState state) {
		super(input, state);
	}

	protected TreeAdaptor adaptor = new CommonTreeAdaptor();

	public void setTreeAdaptor(TreeAdaptor adaptor) {
		this.adaptor = adaptor;
	}
	public TreeAdaptor getTreeAdaptor() {
		return adaptor;
	}
	@Override public String[] getTokenNames() { return DafnyParser.tokenNames; }
	@Override public String getGrammarFileName() { return "Dafny.g"; }


	  protected void mismatch(IntStream input, int ttype, BitSet follow)
	    throws RecognitionException
	  {
	    throw new MismatchedTokenException(ttype, input);
	  }

	  public Object recoverFromMismatchedSet(IntStream input,
	                                         RecognitionException e,
	                                         BitSet follow)
	    throws RecognitionException
	  {
	    throw e;
	  }

	  protected Object recoverFromMismatchedToken(IntStream input, int ttype, BitSet follow)
	    throws RecognitionException
	  {
	    throw new MismatchedTokenException(ttype, input);
	  }


	public static class program_return extends ParserRuleReturnScope {
		DafnyTree tree;
		@Override
		public DafnyTree getTree() { return tree; }
	};


	// $ANTLR start "program"
	// Dafny.g:103:1: program : ( method )+ ;
	public final DafnyParser.program_return program() throws RecognitionException {
		DafnyParser.program_return retval = new DafnyParser.program_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		ParserRuleReturnScope method1 =null;


		try {
			// Dafny.g:103:8: ( ( method )+ )
			// Dafny.g:104:3: ( method )+
			{
			root_0 = (DafnyTree)adaptor.nil();


			// Dafny.g:104:3: ( method )+
			int cnt1=0;
			loop1:
			while (true) {
				int alt1=2;
				int LA1_0 = input.LA(1);
				if ( (LA1_0==LEMMA||LA1_0==METHOD) ) {
					alt1=1;
				}

				switch (alt1) {
				case 1 :
					// Dafny.g:104:3: method
					{
					pushFollow(FOLLOW_method_in_program434);
					method1=method();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, method1.getTree());

					}
					break;

				default :
					if ( cnt1 >= 1 ) break loop1;
					if (state.backtracking>0) {state.failed=true; return retval;}
					EarlyExitException eee = new EarlyExitException(1, input);
					throw eee;
				}
				cnt1++;
			}

			}

			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (DafnyTree)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
		}

		  catch (RecognitionException e) {
		    throw e;
		  }

		finally {
			// do for sure before leaving
		}
		return retval;
	}
	// $ANTLR end "program"


	public static class method_return extends ParserRuleReturnScope {
		DafnyTree tree;
		@Override
		public DafnyTree getTree() { return tree; }
	};


	// $ANTLR start "method"
	// Dafny.g:107:1: method : tok= ( 'method' | 'lemma' ) ID '(' ( vars )? ')' ( returns_ )? ( requires )* ( ensures )* ( decreases )? '{' ( decl )* ( statements )? '}' -> ^( METHOD[tok] ID ^( ARGS ( vars )? ) ( returns_ )? ( requires )* ( ensures )* ( decreases )? ( decl )* ^( BLOCK ( statements )? ) ) ;
	public final DafnyParser.method_return method() throws RecognitionException {
		DafnyParser.method_return retval = new DafnyParser.method_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		Token tok=null;
		Token ID2=null;
		Token char_literal3=null;
		Token char_literal5=null;
		Token char_literal10=null;
		Token char_literal13=null;
		ParserRuleReturnScope vars4 =null;
		ParserRuleReturnScope returns_6 =null;
		ParserRuleReturnScope requires7 =null;
		ParserRuleReturnScope ensures8 =null;
		ParserRuleReturnScope decreases9 =null;
		ParserRuleReturnScope decl11 =null;
		ParserRuleReturnScope statements12 =null;

		DafnyTree tok_tree=null;
		DafnyTree ID2_tree=null;
		DafnyTree char_literal3_tree=null;
		DafnyTree char_literal5_tree=null;
		DafnyTree char_literal10_tree=null;
		DafnyTree char_literal13_tree=null;
		RewriteRuleTokenStream stream_ID=new RewriteRuleTokenStream(adaptor,"token ID");
		RewriteRuleTokenStream stream_BLOCK_BEGIN=new RewriteRuleTokenStream(adaptor,"token BLOCK_BEGIN");
		RewriteRuleTokenStream stream_53=new RewriteRuleTokenStream(adaptor,"token 53");
		RewriteRuleTokenStream stream_LEMMA=new RewriteRuleTokenStream(adaptor,"token LEMMA");
		RewriteRuleTokenStream stream_54=new RewriteRuleTokenStream(adaptor,"token 54");
		RewriteRuleTokenStream stream_METHOD=new RewriteRuleTokenStream(adaptor,"token METHOD");
		RewriteRuleTokenStream stream_BLOCK_END=new RewriteRuleTokenStream(adaptor,"token BLOCK_END");
		RewriteRuleSubtreeStream stream_returns_=new RewriteRuleSubtreeStream(adaptor,"rule returns_");
		RewriteRuleSubtreeStream stream_ensures=new RewriteRuleSubtreeStream(adaptor,"rule ensures");
		RewriteRuleSubtreeStream stream_vars=new RewriteRuleSubtreeStream(adaptor,"rule vars");
		RewriteRuleSubtreeStream stream_decreases=new RewriteRuleSubtreeStream(adaptor,"rule decreases");
		RewriteRuleSubtreeStream stream_statements=new RewriteRuleSubtreeStream(adaptor,"rule statements");
		RewriteRuleSubtreeStream stream_requires=new RewriteRuleSubtreeStream(adaptor,"rule requires");
		RewriteRuleSubtreeStream stream_decl=new RewriteRuleSubtreeStream(adaptor,"rule decl");

		try {
			// Dafny.g:107:7: (tok= ( 'method' | 'lemma' ) ID '(' ( vars )? ')' ( returns_ )? ( requires )* ( ensures )* ( decreases )? '{' ( decl )* ( statements )? '}' -> ^( METHOD[tok] ID ^( ARGS ( vars )? ) ( returns_ )? ( requires )* ( ensures )* ( decreases )? ( decl )* ^( BLOCK ( statements )? ) ) )
			// Dafny.g:108:3: tok= ( 'method' | 'lemma' ) ID '(' ( vars )? ')' ( returns_ )? ( requires )* ( ensures )* ( decreases )? '{' ( decl )* ( statements )? '}'
			{
			// Dafny.g:108:9: ( 'method' | 'lemma' )
			int alt2=2;
			int LA2_0 = input.LA(1);
			if ( (LA2_0==METHOD) ) {
				alt2=1;
			}
			else if ( (LA2_0==LEMMA) ) {
				alt2=2;
			}

			else {
				if (state.backtracking>0) {state.failed=true; return retval;}
				NoViableAltException nvae =
					new NoViableAltException("", 2, 0, input);
				throw nvae;
			}

			switch (alt2) {
				case 1 :
					// Dafny.g:108:10: 'method'
					{
					tok=(Token)match(input,METHOD,FOLLOW_METHOD_in_method453); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_METHOD.add(tok);

					}
					break;
				case 2 :
					// Dafny.g:108:21: 'lemma'
					{
					tok=(Token)match(input,LEMMA,FOLLOW_LEMMA_in_method457); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_LEMMA.add(tok);

					}
					break;

			}

			ID2=(Token)match(input,ID,FOLLOW_ID_in_method462); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_ID.add(ID2);

			char_literal3=(Token)match(input,53,FOLLOW_53_in_method464); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_53.add(char_literal3);

			// Dafny.g:109:10: ( vars )?
			int alt3=2;
			int LA3_0 = input.LA(1);
			if ( (LA3_0==ID) ) {
				alt3=1;
			}
			switch (alt3) {
				case 1 :
					// Dafny.g:109:10: vars
					{
					pushFollow(FOLLOW_vars_in_method466);
					vars4=vars();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_vars.add(vars4.getTree());
					}
					break;

			}

			char_literal5=(Token)match(input,54,FOLLOW_54_in_method469); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_54.add(char_literal5);

			// Dafny.g:110:3: ( returns_ )?
			int alt4=2;
			int LA4_0 = input.LA(1);
			if ( (LA4_0==RETURNS) ) {
				alt4=1;
			}
			switch (alt4) {
				case 1 :
					// Dafny.g:110:5: returns_
					{
					pushFollow(FOLLOW_returns__in_method475);
					returns_6=returns_();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_returns_.add(returns_6.getTree());
					}
					break;

			}

			// Dafny.g:111:3: ( requires )*
			loop5:
			while (true) {
				int alt5=2;
				int LA5_0 = input.LA(1);
				if ( (LA5_0==REQUIRES) ) {
					alt5=1;
				}

				switch (alt5) {
				case 1 :
					// Dafny.g:111:5: requires
					{
					pushFollow(FOLLOW_requires_in_method484);
					requires7=requires();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_requires.add(requires7.getTree());
					}
					break;

				default :
					break loop5;
				}
			}

			// Dafny.g:112:3: ( ensures )*
			loop6:
			while (true) {
				int alt6=2;
				int LA6_0 = input.LA(1);
				if ( (LA6_0==ENSURES) ) {
					alt6=1;
				}

				switch (alt6) {
				case 1 :
					// Dafny.g:112:5: ensures
					{
					pushFollow(FOLLOW_ensures_in_method493);
					ensures8=ensures();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_ensures.add(ensures8.getTree());
					}
					break;

				default :
					break loop6;
				}
			}

			// Dafny.g:113:3: ( decreases )?
			int alt7=2;
			int LA7_0 = input.LA(1);
			if ( (LA7_0==DECREASES) ) {
				alt7=1;
			}
			switch (alt7) {
				case 1 :
					// Dafny.g:113:5: decreases
					{
					pushFollow(FOLLOW_decreases_in_method502);
					decreases9=decreases();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_decreases.add(decreases9.getTree());
					}
					break;

			}

			char_literal10=(Token)match(input,BLOCK_BEGIN,FOLLOW_BLOCK_BEGIN_in_method509); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_BLOCK_BEGIN.add(char_literal10);

			// Dafny.g:114:7: ( decl )*
			loop8:
			while (true) {
				int alt8=2;
				int LA8_0 = input.LA(1);
				if ( (LA8_0==VAR) ) {
					alt8=1;
				}

				switch (alt8) {
				case 1 :
					// Dafny.g:114:9: decl
					{
					pushFollow(FOLLOW_decl_in_method513);
					decl11=decl();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_decl.add(decl11.getTree());
					}
					break;

				default :
					break loop8;
				}
			}

			// Dafny.g:114:17: ( statements )?
			int alt9=2;
			int LA9_0 = input.LA(1);
			if ( (LA9_0==ASSERT||(LA9_0 >= ID && LA9_0 <= IF)||LA9_0==LABEL||LA9_0==WHILE) ) {
				alt9=1;
			}
			switch (alt9) {
				case 1 :
					// Dafny.g:114:17: statements
					{
					pushFollow(FOLLOW_statements_in_method518);
					statements12=statements();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_statements.add(statements12.getTree());
					}
					break;

			}

			char_literal13=(Token)match(input,BLOCK_END,FOLLOW_BLOCK_END_in_method521); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_BLOCK_END.add(char_literal13);

			// AST REWRITE
			// elements: decl, decreases, returns_, statements, ID, ensures, requires, vars
			// token labels: 
			// rule labels: retval
			// token list labels: 
			// rule list labels: 
			// wildcard labels: 
			if ( state.backtracking==0 ) {
			retval.tree = root_0;
			RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

			root_0 = (DafnyTree)adaptor.nil();
			// 115:3: -> ^( METHOD[tok] ID ^( ARGS ( vars )? ) ( returns_ )? ( requires )* ( ensures )* ( decreases )? ( decl )* ^( BLOCK ( statements )? ) )
			{
				// Dafny.g:116:5: ^( METHOD[tok] ID ^( ARGS ( vars )? ) ( returns_ )? ( requires )* ( ensures )* ( decreases )? ( decl )* ^( BLOCK ( statements )? ) )
				{
				DafnyTree root_1 = (DafnyTree)adaptor.nil();
				root_1 = (DafnyTree)adaptor.becomeRoot((DafnyTree)adaptor.create(METHOD, tok), root_1);
				adaptor.addChild(root_1, stream_ID.nextNode());
				// Dafny.g:116:22: ^( ARGS ( vars )? )
				{
				DafnyTree root_2 = (DafnyTree)adaptor.nil();
				root_2 = (DafnyTree)adaptor.becomeRoot((DafnyTree)adaptor.create(ARGS, "ARGS"), root_2);
				// Dafny.g:116:29: ( vars )?
				if ( stream_vars.hasNext() ) {
					adaptor.addChild(root_2, stream_vars.nextTree());
				}
				stream_vars.reset();

				adaptor.addChild(root_1, root_2);
				}

				// Dafny.g:116:36: ( returns_ )?
				if ( stream_returns_.hasNext() ) {
					adaptor.addChild(root_1, stream_returns_.nextTree());
				}
				stream_returns_.reset();

				// Dafny.g:116:46: ( requires )*
				while ( stream_requires.hasNext() ) {
					adaptor.addChild(root_1, stream_requires.nextTree());
				}
				stream_requires.reset();

				// Dafny.g:116:56: ( ensures )*
				while ( stream_ensures.hasNext() ) {
					adaptor.addChild(root_1, stream_ensures.nextTree());
				}
				stream_ensures.reset();

				// Dafny.g:117:9: ( decreases )?
				if ( stream_decreases.hasNext() ) {
					adaptor.addChild(root_1, stream_decreases.nextTree());
				}
				stream_decreases.reset();

				// Dafny.g:117:20: ( decl )*
				while ( stream_decl.hasNext() ) {
					adaptor.addChild(root_1, stream_decl.nextTree());
				}
				stream_decl.reset();

				// Dafny.g:117:26: ^( BLOCK ( statements )? )
				{
				DafnyTree root_2 = (DafnyTree)adaptor.nil();
				root_2 = (DafnyTree)adaptor.becomeRoot((DafnyTree)adaptor.create(BLOCK, "BLOCK"), root_2);
				// Dafny.g:117:34: ( statements )?
				if ( stream_statements.hasNext() ) {
					adaptor.addChild(root_2, stream_statements.nextTree());
				}
				stream_statements.reset();

				adaptor.addChild(root_1, root_2);
				}

				adaptor.addChild(root_0, root_1);
				}

			}


			retval.tree = root_0;
			}

			}

			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (DafnyTree)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
		}

		  catch (RecognitionException e) {
		    throw e;
		  }

		finally {
			// do for sure before leaving
		}
		return retval;
	}
	// $ANTLR end "method"


	public static class decl_return extends ParserRuleReturnScope {
		DafnyTree tree;
		@Override
		public DafnyTree getTree() { return tree; }
	};


	// $ANTLR start "decl"
	// Dafny.g:120:1: decl : VAR ! var ';' !;
	public final DafnyParser.decl_return decl() throws RecognitionException {
		DafnyParser.decl_return retval = new DafnyParser.decl_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		Token VAR14=null;
		Token char_literal16=null;
		ParserRuleReturnScope var15 =null;

		DafnyTree VAR14_tree=null;
		DafnyTree char_literal16_tree=null;

		try {
			// Dafny.g:120:5: ( VAR ! var ';' !)
			// Dafny.g:121:3: VAR ! var ';' !
			{
			root_0 = (DafnyTree)adaptor.nil();


			VAR14=(Token)match(input,VAR,FOLLOW_VAR_in_decl586); if (state.failed) return retval;
			pushFollow(FOLLOW_var_in_decl589);
			var15=var();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, var15.getTree());

			char_literal16=(Token)match(input,57,FOLLOW_57_in_decl591); if (state.failed) return retval;
			}

			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (DafnyTree)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
		}

		  catch (RecognitionException e) {
		    throw e;
		  }

		finally {
			// do for sure before leaving
		}
		return retval;
	}
	// $ANTLR end "decl"


	public static class vars_return extends ParserRuleReturnScope {
		DafnyTree tree;
		@Override
		public DafnyTree getTree() { return tree; }
	};


	// $ANTLR start "vars"
	// Dafny.g:124:1: vars : var ( ',' ! var )* ;
	public final DafnyParser.vars_return vars() throws RecognitionException {
		DafnyParser.vars_return retval = new DafnyParser.vars_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		Token char_literal18=null;
		ParserRuleReturnScope var17 =null;
		ParserRuleReturnScope var19 =null;

		DafnyTree char_literal18_tree=null;

		try {
			// Dafny.g:124:5: ( var ( ',' ! var )* )
			// Dafny.g:125:3: var ( ',' ! var )*
			{
			root_0 = (DafnyTree)adaptor.nil();


			pushFollow(FOLLOW_var_in_vars604);
			var17=var();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, var17.getTree());

			// Dafny.g:126:3: ( ',' ! var )*
			loop10:
			while (true) {
				int alt10=2;
				int LA10_0 = input.LA(1);
				if ( (LA10_0==55) ) {
					alt10=1;
				}

				switch (alt10) {
				case 1 :
					// Dafny.g:126:5: ',' ! var
					{
					char_literal18=(Token)match(input,55,FOLLOW_55_in_vars610); if (state.failed) return retval;
					pushFollow(FOLLOW_var_in_vars613);
					var19=var();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, var19.getTree());

					}
					break;

				default :
					break loop10;
				}
			}

			}

			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (DafnyTree)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
		}

		  catch (RecognitionException e) {
		    throw e;
		  }

		finally {
			// do for sure before leaving
		}
		return retval;
	}
	// $ANTLR end "vars"


	public static class var_return extends ParserRuleReturnScope {
		DafnyTree tree;
		@Override
		public DafnyTree getTree() { return tree; }
	};


	// $ANTLR start "var"
	// Dafny.g:129:1: var : ID ':' type -> ^( VAR ID type ) ;
	public final DafnyParser.var_return var() throws RecognitionException {
		DafnyParser.var_return retval = new DafnyParser.var_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		Token ID20=null;
		Token char_literal21=null;
		ParserRuleReturnScope type22 =null;

		DafnyTree ID20_tree=null;
		DafnyTree char_literal21_tree=null;
		RewriteRuleTokenStream stream_56=new RewriteRuleTokenStream(adaptor,"token 56");
		RewriteRuleTokenStream stream_ID=new RewriteRuleTokenStream(adaptor,"token ID");
		RewriteRuleSubtreeStream stream_type=new RewriteRuleSubtreeStream(adaptor,"rule type");

		try {
			// Dafny.g:129:4: ( ID ':' type -> ^( VAR ID type ) )
			// Dafny.g:130:3: ID ':' type
			{
			ID20=(Token)match(input,ID,FOLLOW_ID_in_var628); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_ID.add(ID20);

			char_literal21=(Token)match(input,56,FOLLOW_56_in_var630); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_56.add(char_literal21);

			pushFollow(FOLLOW_type_in_var632);
			type22=type();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) stream_type.add(type22.getTree());
			// AST REWRITE
			// elements: ID, type
			// token labels: 
			// rule labels: retval
			// token list labels: 
			// rule list labels: 
			// wildcard labels: 
			if ( state.backtracking==0 ) {
			retval.tree = root_0;
			RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

			root_0 = (DafnyTree)adaptor.nil();
			// 130:15: -> ^( VAR ID type )
			{
				// Dafny.g:130:18: ^( VAR ID type )
				{
				DafnyTree root_1 = (DafnyTree)adaptor.nil();
				root_1 = (DafnyTree)adaptor.becomeRoot((DafnyTree)adaptor.create(VAR, "VAR"), root_1);
				adaptor.addChild(root_1, stream_ID.nextNode());
				adaptor.addChild(root_1, stream_type.nextTree());
				adaptor.addChild(root_0, root_1);
				}

			}


			retval.tree = root_0;
			}

			}

			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (DafnyTree)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
		}

		  catch (RecognitionException e) {
		    throw e;
		  }

		finally {
			// do for sure before leaving
		}
		return retval;
	}
	// $ANTLR end "var"


	public static class type_return extends ParserRuleReturnScope {
		DafnyTree tree;
		@Override
		public DafnyTree getTree() { return tree; }
	};


	// $ANTLR start "type"
	// Dafny.g:133:1: type : ( INT | SET ^ '<' ! INT '>' !| ARRAY ^ '<' ! INT '>' !);
	public final DafnyParser.type_return type() throws RecognitionException {
		DafnyParser.type_return retval = new DafnyParser.type_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		Token INT23=null;
		Token SET24=null;
		Token char_literal25=null;
		Token INT26=null;
		Token char_literal27=null;
		Token ARRAY28=null;
		Token char_literal29=null;
		Token INT30=null;
		Token char_literal31=null;

		DafnyTree INT23_tree=null;
		DafnyTree SET24_tree=null;
		DafnyTree char_literal25_tree=null;
		DafnyTree INT26_tree=null;
		DafnyTree char_literal27_tree=null;
		DafnyTree ARRAY28_tree=null;
		DafnyTree char_literal29_tree=null;
		DafnyTree INT30_tree=null;
		DafnyTree char_literal31_tree=null;

		try {
			// Dafny.g:133:5: ( INT | SET ^ '<' ! INT '>' !| ARRAY ^ '<' ! INT '>' !)
			int alt11=3;
			switch ( input.LA(1) ) {
			case INT:
				{
				alt11=1;
				}
				break;
			case SET:
				{
				alt11=2;
				}
				break;
			case ARRAY:
				{
				alt11=3;
				}
				break;
			default:
				if (state.backtracking>0) {state.failed=true; return retval;}
				NoViableAltException nvae =
					new NoViableAltException("", 11, 0, input);
				throw nvae;
			}
			switch (alt11) {
				case 1 :
					// Dafny.g:134:5: INT
					{
					root_0 = (DafnyTree)adaptor.nil();


					INT23=(Token)match(input,INT,FOLLOW_INT_in_type656); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					INT23_tree = (DafnyTree)adaptor.create(INT23);
					adaptor.addChild(root_0, INT23_tree);
					}

					}
					break;
				case 2 :
					// Dafny.g:134:11: SET ^ '<' ! INT '>' !
					{
					root_0 = (DafnyTree)adaptor.nil();


					SET24=(Token)match(input,SET,FOLLOW_SET_in_type660); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					SET24_tree = (DafnyTree)adaptor.create(SET24);
					root_0 = (DafnyTree)adaptor.becomeRoot(SET24_tree, root_0);
					}

					char_literal25=(Token)match(input,LT,FOLLOW_LT_in_type663); if (state.failed) return retval;
					INT26=(Token)match(input,INT,FOLLOW_INT_in_type666); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					INT26_tree = (DafnyTree)adaptor.create(INT26);
					adaptor.addChild(root_0, INT26_tree);
					}

					char_literal27=(Token)match(input,GT,FOLLOW_GT_in_type668); if (state.failed) return retval;
					}
					break;
				case 3 :
					// Dafny.g:135:5: ARRAY ^ '<' ! INT '>' !
					{
					root_0 = (DafnyTree)adaptor.nil();


					ARRAY28=(Token)match(input,ARRAY,FOLLOW_ARRAY_in_type675); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					ARRAY28_tree = (DafnyTree)adaptor.create(ARRAY28);
					root_0 = (DafnyTree)adaptor.becomeRoot(ARRAY28_tree, root_0);
					}

					char_literal29=(Token)match(input,LT,FOLLOW_LT_in_type678); if (state.failed) return retval;
					INT30=(Token)match(input,INT,FOLLOW_INT_in_type681); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					INT30_tree = (DafnyTree)adaptor.create(INT30);
					adaptor.addChild(root_0, INT30_tree);
					}

					char_literal31=(Token)match(input,GT,FOLLOW_GT_in_type683); if (state.failed) return retval;
					}
					break;

			}
			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (DafnyTree)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
		}

		  catch (RecognitionException e) {
		    throw e;
		  }

		finally {
			// do for sure before leaving
		}
		return retval;
	}
	// $ANTLR end "type"


	public static class returns__return extends ParserRuleReturnScope {
		DafnyTree tree;
		@Override
		public DafnyTree getTree() { return tree; }
	};


	// $ANTLR start "returns_"
	// Dafny.g:138:1: returns_ : RETURNS ^ '(' ! vars ')' !;
	public final DafnyParser.returns__return returns_() throws RecognitionException {
		DafnyParser.returns__return retval = new DafnyParser.returns__return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		Token RETURNS32=null;
		Token char_literal33=null;
		Token char_literal35=null;
		ParserRuleReturnScope vars34 =null;

		DafnyTree RETURNS32_tree=null;
		DafnyTree char_literal33_tree=null;
		DafnyTree char_literal35_tree=null;

		try {
			// Dafny.g:138:9: ( RETURNS ^ '(' ! vars ')' !)
			// Dafny.g:139:3: RETURNS ^ '(' ! vars ')' !
			{
			root_0 = (DafnyTree)adaptor.nil();


			RETURNS32=(Token)match(input,RETURNS,FOLLOW_RETURNS_in_returns_696); if (state.failed) return retval;
			if ( state.backtracking==0 ) {
			RETURNS32_tree = (DafnyTree)adaptor.create(RETURNS32);
			root_0 = (DafnyTree)adaptor.becomeRoot(RETURNS32_tree, root_0);
			}

			char_literal33=(Token)match(input,53,FOLLOW_53_in_returns_699); if (state.failed) return retval;
			pushFollow(FOLLOW_vars_in_returns_702);
			vars34=vars();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, vars34.getTree());

			char_literal35=(Token)match(input,54,FOLLOW_54_in_returns_704); if (state.failed) return retval;
			}

			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (DafnyTree)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
		}

		  catch (RecognitionException e) {
		    throw e;
		  }

		finally {
			// do for sure before leaving
		}
		return retval;
	}
	// $ANTLR end "returns_"


	public static class requires_return extends ParserRuleReturnScope {
		DafnyTree tree;
		@Override
		public DafnyTree getTree() { return tree; }
	};


	// $ANTLR start "requires"
	// Dafny.g:142:1: requires : REQUIRES ^ ( 'label' ! ID ':' !)? expression ;
	public final DafnyParser.requires_return requires() throws RecognitionException {
		DafnyParser.requires_return retval = new DafnyParser.requires_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		Token REQUIRES36=null;
		Token string_literal37=null;
		Token ID38=null;
		Token char_literal39=null;
		ParserRuleReturnScope expression40 =null;

		DafnyTree REQUIRES36_tree=null;
		DafnyTree string_literal37_tree=null;
		DafnyTree ID38_tree=null;
		DafnyTree char_literal39_tree=null;

		try {
			// Dafny.g:142:9: ( REQUIRES ^ ( 'label' ! ID ':' !)? expression )
			// Dafny.g:143:3: REQUIRES ^ ( 'label' ! ID ':' !)? expression
			{
			root_0 = (DafnyTree)adaptor.nil();


			REQUIRES36=(Token)match(input,REQUIRES,FOLLOW_REQUIRES_in_requires717); if (state.failed) return retval;
			if ( state.backtracking==0 ) {
			REQUIRES36_tree = (DafnyTree)adaptor.create(REQUIRES36);
			root_0 = (DafnyTree)adaptor.becomeRoot(REQUIRES36_tree, root_0);
			}

			// Dafny.g:143:13: ( 'label' ! ID ':' !)?
			int alt12=2;
			int LA12_0 = input.LA(1);
			if ( (LA12_0==LABEL) ) {
				alt12=1;
			}
			switch (alt12) {
				case 1 :
					// Dafny.g:143:14: 'label' ! ID ':' !
					{
					string_literal37=(Token)match(input,LABEL,FOLLOW_LABEL_in_requires721); if (state.failed) return retval;
					ID38=(Token)match(input,ID,FOLLOW_ID_in_requires724); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					ID38_tree = (DafnyTree)adaptor.create(ID38);
					adaptor.addChild(root_0, ID38_tree);
					}

					char_literal39=(Token)match(input,56,FOLLOW_56_in_requires726); if (state.failed) return retval;
					}
					break;

			}

			pushFollow(FOLLOW_expression_in_requires731);
			expression40=expression();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, expression40.getTree());

			}

			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (DafnyTree)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
		}

		  catch (RecognitionException e) {
		    throw e;
		  }

		finally {
			// do for sure before leaving
		}
		return retval;
	}
	// $ANTLR end "requires"


	public static class ensures_return extends ParserRuleReturnScope {
		DafnyTree tree;
		@Override
		public DafnyTree getTree() { return tree; }
	};


	// $ANTLR start "ensures"
	// Dafny.g:146:1: ensures : ENSURES ^ ( 'label' ! ID ':' !)? expression ;
	public final DafnyParser.ensures_return ensures() throws RecognitionException {
		DafnyParser.ensures_return retval = new DafnyParser.ensures_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		Token ENSURES41=null;
		Token string_literal42=null;
		Token ID43=null;
		Token char_literal44=null;
		ParserRuleReturnScope expression45 =null;

		DafnyTree ENSURES41_tree=null;
		DafnyTree string_literal42_tree=null;
		DafnyTree ID43_tree=null;
		DafnyTree char_literal44_tree=null;

		try {
			// Dafny.g:146:8: ( ENSURES ^ ( 'label' ! ID ':' !)? expression )
			// Dafny.g:147:3: ENSURES ^ ( 'label' ! ID ':' !)? expression
			{
			root_0 = (DafnyTree)adaptor.nil();


			ENSURES41=(Token)match(input,ENSURES,FOLLOW_ENSURES_in_ensures743); if (state.failed) return retval;
			if ( state.backtracking==0 ) {
			ENSURES41_tree = (DafnyTree)adaptor.create(ENSURES41);
			root_0 = (DafnyTree)adaptor.becomeRoot(ENSURES41_tree, root_0);
			}

			// Dafny.g:147:12: ( 'label' ! ID ':' !)?
			int alt13=2;
			int LA13_0 = input.LA(1);
			if ( (LA13_0==LABEL) ) {
				alt13=1;
			}
			switch (alt13) {
				case 1 :
					// Dafny.g:147:13: 'label' ! ID ':' !
					{
					string_literal42=(Token)match(input,LABEL,FOLLOW_LABEL_in_ensures747); if (state.failed) return retval;
					ID43=(Token)match(input,ID,FOLLOW_ID_in_ensures750); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					ID43_tree = (DafnyTree)adaptor.create(ID43);
					adaptor.addChild(root_0, ID43_tree);
					}

					char_literal44=(Token)match(input,56,FOLLOW_56_in_ensures752); if (state.failed) return retval;
					}
					break;

			}

			pushFollow(FOLLOW_expression_in_ensures757);
			expression45=expression();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, expression45.getTree());

			}

			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (DafnyTree)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
		}

		  catch (RecognitionException e) {
		    throw e;
		  }

		finally {
			// do for sure before leaving
		}
		return retval;
	}
	// $ANTLR end "ensures"


	public static class decreases_return extends ParserRuleReturnScope {
		DafnyTree tree;
		@Override
		public DafnyTree getTree() { return tree; }
	};


	// $ANTLR start "decreases"
	// Dafny.g:150:1: decreases : DECREASES ^ expression ;
	public final DafnyParser.decreases_return decreases() throws RecognitionException {
		DafnyParser.decreases_return retval = new DafnyParser.decreases_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		Token DECREASES46=null;
		ParserRuleReturnScope expression47 =null;

		DafnyTree DECREASES46_tree=null;

		try {
			// Dafny.g:150:10: ( DECREASES ^ expression )
			// Dafny.g:151:3: DECREASES ^ expression
			{
			root_0 = (DafnyTree)adaptor.nil();


			DECREASES46=(Token)match(input,DECREASES,FOLLOW_DECREASES_in_decreases769); if (state.failed) return retval;
			if ( state.backtracking==0 ) {
			DECREASES46_tree = (DafnyTree)adaptor.create(DECREASES46);
			root_0 = (DafnyTree)adaptor.becomeRoot(DECREASES46_tree, root_0);
			}

			pushFollow(FOLLOW_expression_in_decreases772);
			expression47=expression();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, expression47.getTree());

			}

			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (DafnyTree)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
		}

		  catch (RecognitionException e) {
		    throw e;
		  }

		finally {
			// do for sure before leaving
		}
		return retval;
	}
	// $ANTLR end "decreases"


	public static class invariant_return extends ParserRuleReturnScope {
		DafnyTree tree;
		@Override
		public DafnyTree getTree() { return tree; }
	};


	// $ANTLR start "invariant"
	// Dafny.g:154:1: invariant : INVARIANT ^ ( 'label' ! ID ':' !)? expression ;
	public final DafnyParser.invariant_return invariant() throws RecognitionException {
		DafnyParser.invariant_return retval = new DafnyParser.invariant_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		Token INVARIANT48=null;
		Token string_literal49=null;
		Token ID50=null;
		Token char_literal51=null;
		ParserRuleReturnScope expression52 =null;

		DafnyTree INVARIANT48_tree=null;
		DafnyTree string_literal49_tree=null;
		DafnyTree ID50_tree=null;
		DafnyTree char_literal51_tree=null;

		try {
			// Dafny.g:154:10: ( INVARIANT ^ ( 'label' ! ID ':' !)? expression )
			// Dafny.g:155:3: INVARIANT ^ ( 'label' ! ID ':' !)? expression
			{
			root_0 = (DafnyTree)adaptor.nil();


			INVARIANT48=(Token)match(input,INVARIANT,FOLLOW_INVARIANT_in_invariant784); if (state.failed) return retval;
			if ( state.backtracking==0 ) {
			INVARIANT48_tree = (DafnyTree)adaptor.create(INVARIANT48);
			root_0 = (DafnyTree)adaptor.becomeRoot(INVARIANT48_tree, root_0);
			}

			// Dafny.g:155:14: ( 'label' ! ID ':' !)?
			int alt14=2;
			int LA14_0 = input.LA(1);
			if ( (LA14_0==LABEL) ) {
				alt14=1;
			}
			switch (alt14) {
				case 1 :
					// Dafny.g:155:15: 'label' ! ID ':' !
					{
					string_literal49=(Token)match(input,LABEL,FOLLOW_LABEL_in_invariant788); if (state.failed) return retval;
					ID50=(Token)match(input,ID,FOLLOW_ID_in_invariant791); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					ID50_tree = (DafnyTree)adaptor.create(ID50);
					adaptor.addChild(root_0, ID50_tree);
					}

					char_literal51=(Token)match(input,56,FOLLOW_56_in_invariant793); if (state.failed) return retval;
					}
					break;

			}

			pushFollow(FOLLOW_expression_in_invariant798);
			expression52=expression();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, expression52.getTree());

			}

			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (DafnyTree)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
		}

		  catch (RecognitionException e) {
		    throw e;
		  }

		finally {
			// do for sure before leaving
		}
		return retval;
	}
	// $ANTLR end "invariant"


	public static class block_return extends ParserRuleReturnScope {
		DafnyTree tree;
		@Override
		public DafnyTree getTree() { return tree; }
	};


	// $ANTLR start "block"
	// Dafny.g:158:1: block : '{' ( statements )? '}' -> ^( BLOCK ( statements )? ) ;
	public final DafnyParser.block_return block() throws RecognitionException {
		DafnyParser.block_return retval = new DafnyParser.block_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		Token char_literal53=null;
		Token char_literal55=null;
		ParserRuleReturnScope statements54 =null;

		DafnyTree char_literal53_tree=null;
		DafnyTree char_literal55_tree=null;
		RewriteRuleTokenStream stream_BLOCK_BEGIN=new RewriteRuleTokenStream(adaptor,"token BLOCK_BEGIN");
		RewriteRuleTokenStream stream_BLOCK_END=new RewriteRuleTokenStream(adaptor,"token BLOCK_END");
		RewriteRuleSubtreeStream stream_statements=new RewriteRuleSubtreeStream(adaptor,"rule statements");

		try {
			// Dafny.g:158:6: ( '{' ( statements )? '}' -> ^( BLOCK ( statements )? ) )
			// Dafny.g:159:3: '{' ( statements )? '}'
			{
			char_literal53=(Token)match(input,BLOCK_BEGIN,FOLLOW_BLOCK_BEGIN_in_block810); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_BLOCK_BEGIN.add(char_literal53);

			// Dafny.g:159:7: ( statements )?
			int alt15=2;
			int LA15_0 = input.LA(1);
			if ( (LA15_0==ASSERT||(LA15_0 >= ID && LA15_0 <= IF)||LA15_0==LABEL||LA15_0==WHILE) ) {
				alt15=1;
			}
			switch (alt15) {
				case 1 :
					// Dafny.g:159:7: statements
					{
					pushFollow(FOLLOW_statements_in_block812);
					statements54=statements();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_statements.add(statements54.getTree());
					}
					break;

			}

			char_literal55=(Token)match(input,BLOCK_END,FOLLOW_BLOCK_END_in_block815); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_BLOCK_END.add(char_literal55);

			// AST REWRITE
			// elements: statements
			// token labels: 
			// rule labels: retval
			// token list labels: 
			// rule list labels: 
			// wildcard labels: 
			if ( state.backtracking==0 ) {
			retval.tree = root_0;
			RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

			root_0 = (DafnyTree)adaptor.nil();
			// 159:23: -> ^( BLOCK ( statements )? )
			{
				// Dafny.g:159:26: ^( BLOCK ( statements )? )
				{
				DafnyTree root_1 = (DafnyTree)adaptor.nil();
				root_1 = (DafnyTree)adaptor.becomeRoot((DafnyTree)adaptor.create(BLOCK, "BLOCK"), root_1);
				// Dafny.g:159:34: ( statements )?
				if ( stream_statements.hasNext() ) {
					adaptor.addChild(root_1, stream_statements.nextTree());
				}
				stream_statements.reset();

				adaptor.addChild(root_0, root_1);
				}

			}


			retval.tree = root_0;
			}

			}

			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (DafnyTree)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
		}

		  catch (RecognitionException e) {
		    throw e;
		  }

		finally {
			// do for sure before leaving
		}
		return retval;
	}
	// $ANTLR end "block"


	public static class relaxedBlock_return extends ParserRuleReturnScope {
		DafnyTree tree;
		@Override
		public DafnyTree getTree() { return tree; }
	};


	// $ANTLR start "relaxedBlock"
	// Dafny.g:162:1: relaxedBlock : ( block | statement -> ^( BLOCK statement ) );
	public final DafnyParser.relaxedBlock_return relaxedBlock() throws RecognitionException {
		DafnyParser.relaxedBlock_return retval = new DafnyParser.relaxedBlock_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		ParserRuleReturnScope block56 =null;
		ParserRuleReturnScope statement57 =null;

		RewriteRuleSubtreeStream stream_statement=new RewriteRuleSubtreeStream(adaptor,"rule statement");

		try {
			// Dafny.g:162:13: ( block | statement -> ^( BLOCK statement ) )
			int alt16=2;
			int LA16_0 = input.LA(1);
			if ( (LA16_0==BLOCK_BEGIN) ) {
				alt16=1;
			}
			else if ( (LA16_0==ASSERT||(LA16_0 >= ID && LA16_0 <= IF)||LA16_0==LABEL||LA16_0==WHILE) ) {
				alt16=2;
			}

			else {
				if (state.backtracking>0) {state.failed=true; return retval;}
				NoViableAltException nvae =
					new NoViableAltException("", 16, 0, input);
				throw nvae;
			}

			switch (alt16) {
				case 1 :
					// Dafny.g:163:5: block
					{
					root_0 = (DafnyTree)adaptor.nil();


					pushFollow(FOLLOW_block_in_relaxedBlock838);
					block56=block();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, block56.getTree());

					}
					break;
				case 2 :
					// Dafny.g:164:5: statement
					{
					pushFollow(FOLLOW_statement_in_relaxedBlock844);
					statement57=statement();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_statement.add(statement57.getTree());
					// AST REWRITE
					// elements: statement
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (DafnyTree)adaptor.nil();
					// 164:15: -> ^( BLOCK statement )
					{
						// Dafny.g:164:18: ^( BLOCK statement )
						{
						DafnyTree root_1 = (DafnyTree)adaptor.nil();
						root_1 = (DafnyTree)adaptor.becomeRoot((DafnyTree)adaptor.create(BLOCK, "BLOCK"), root_1);
						adaptor.addChild(root_1, stream_statement.nextTree());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;

			}
			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (DafnyTree)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
		}

		  catch (RecognitionException e) {
		    throw e;
		  }

		finally {
			// do for sure before leaving
		}
		return retval;
	}
	// $ANTLR end "relaxedBlock"


	public static class statements_return extends ParserRuleReturnScope {
		DafnyTree tree;
		@Override
		public DafnyTree getTree() { return tree; }
	};


	// $ANTLR start "statements"
	// Dafny.g:167:1: statements : ( statement )+ ;
	public final DafnyParser.statements_return statements() throws RecognitionException {
		DafnyParser.statements_return retval = new DafnyParser.statements_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		ParserRuleReturnScope statement58 =null;


		try {
			// Dafny.g:167:11: ( ( statement )+ )
			// Dafny.g:168:3: ( statement )+
			{
			root_0 = (DafnyTree)adaptor.nil();


			// Dafny.g:168:3: ( statement )+
			int cnt17=0;
			loop17:
			while (true) {
				int alt17=2;
				int LA17_0 = input.LA(1);
				if ( (LA17_0==ASSERT||(LA17_0 >= ID && LA17_0 <= IF)||LA17_0==LABEL||LA17_0==WHILE) ) {
					alt17=1;
				}

				switch (alt17) {
				case 1 :
					// Dafny.g:168:5: statement
					{
					pushFollow(FOLLOW_statement_in_statements866);
					statement58=statement();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, statement58.getTree());

					}
					break;

				default :
					if ( cnt17 >= 1 ) break loop17;
					if (state.backtracking>0) {state.failed=true; return retval;}
					EarlyExitException eee = new EarlyExitException(17, input);
					throw eee;
				}
				cnt17++;
			}

			}

			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (DafnyTree)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
		}

		  catch (RecognitionException e) {
		    throw e;
		  }

		finally {
			// do for sure before leaving
		}
		return retval;
	}
	// $ANTLR end "statements"


	public static class statement_return extends ParserRuleReturnScope {
		DafnyTree tree;
		@Override
		public DafnyTree getTree() { return tree; }
	};


	// $ANTLR start "statement"
	// Dafny.g:171:1: statement : ( ID ':=' ^ expression ';' !| ( ID ':=' 'call' )=>r= ID ':=' 'call' f= ID '(' ( expressions )? ')' ';' -> ^( 'call' $f ^( RESULTS $r) ^( ARGS ( expressions )? ) ) | ids ':=' 'call' ID '(' ( expressions )? ')' ';' -> ^( 'call' ID ^( RESULTS ids ) ^( ARGS ( expressions )? ) ) | ( 'label' ID ':' )? 'while' expression ( invariant )+ decreases relaxedBlock -> ^( 'while' ( ID )? expression ( invariant )+ decreases relaxedBlock ) | 'if' ^ expression relaxedBlock ( options {greedy=true; } : 'else' ! relaxedBlock )? | 'assert' ^ ( 'label' ! ID ':' !)? expression ';' !);
	public final DafnyParser.statement_return statement() throws RecognitionException {
		DafnyParser.statement_return retval = new DafnyParser.statement_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		Token r=null;
		Token f=null;
		Token ID59=null;
		Token string_literal60=null;
		Token char_literal62=null;
		Token string_literal63=null;
		Token string_literal64=null;
		Token char_literal65=null;
		Token char_literal67=null;
		Token char_literal68=null;
		Token string_literal70=null;
		Token string_literal71=null;
		Token ID72=null;
		Token char_literal73=null;
		Token char_literal75=null;
		Token char_literal76=null;
		Token string_literal77=null;
		Token ID78=null;
		Token char_literal79=null;
		Token string_literal80=null;
		Token string_literal85=null;
		Token string_literal88=null;
		Token string_literal90=null;
		Token string_literal91=null;
		Token ID92=null;
		Token char_literal93=null;
		Token char_literal95=null;
		ParserRuleReturnScope expression61 =null;
		ParserRuleReturnScope expressions66 =null;
		ParserRuleReturnScope ids69 =null;
		ParserRuleReturnScope expressions74 =null;
		ParserRuleReturnScope expression81 =null;
		ParserRuleReturnScope invariant82 =null;
		ParserRuleReturnScope decreases83 =null;
		ParserRuleReturnScope relaxedBlock84 =null;
		ParserRuleReturnScope expression86 =null;
		ParserRuleReturnScope relaxedBlock87 =null;
		ParserRuleReturnScope relaxedBlock89 =null;
		ParserRuleReturnScope expression94 =null;

		DafnyTree r_tree=null;
		DafnyTree f_tree=null;
		DafnyTree ID59_tree=null;
		DafnyTree string_literal60_tree=null;
		DafnyTree char_literal62_tree=null;
		DafnyTree string_literal63_tree=null;
		DafnyTree string_literal64_tree=null;
		DafnyTree char_literal65_tree=null;
		DafnyTree char_literal67_tree=null;
		DafnyTree char_literal68_tree=null;
		DafnyTree string_literal70_tree=null;
		DafnyTree string_literal71_tree=null;
		DafnyTree ID72_tree=null;
		DafnyTree char_literal73_tree=null;
		DafnyTree char_literal75_tree=null;
		DafnyTree char_literal76_tree=null;
		DafnyTree string_literal77_tree=null;
		DafnyTree ID78_tree=null;
		DafnyTree char_literal79_tree=null;
		DafnyTree string_literal80_tree=null;
		DafnyTree string_literal85_tree=null;
		DafnyTree string_literal88_tree=null;
		DafnyTree string_literal90_tree=null;
		DafnyTree string_literal91_tree=null;
		DafnyTree ID92_tree=null;
		DafnyTree char_literal93_tree=null;
		DafnyTree char_literal95_tree=null;
		RewriteRuleTokenStream stream_CALL=new RewriteRuleTokenStream(adaptor,"token CALL");
		RewriteRuleTokenStream stream_57=new RewriteRuleTokenStream(adaptor,"token 57");
		RewriteRuleTokenStream stream_56=new RewriteRuleTokenStream(adaptor,"token 56");
		RewriteRuleTokenStream stream_WHILE=new RewriteRuleTokenStream(adaptor,"token WHILE");
		RewriteRuleTokenStream stream_LABEL=new RewriteRuleTokenStream(adaptor,"token LABEL");
		RewriteRuleTokenStream stream_ID=new RewriteRuleTokenStream(adaptor,"token ID");
		RewriteRuleTokenStream stream_53=new RewriteRuleTokenStream(adaptor,"token 53");
		RewriteRuleTokenStream stream_54=new RewriteRuleTokenStream(adaptor,"token 54");
		RewriteRuleTokenStream stream_ASSIGN=new RewriteRuleTokenStream(adaptor,"token ASSIGN");
		RewriteRuleSubtreeStream stream_expression=new RewriteRuleSubtreeStream(adaptor,"rule expression");
		RewriteRuleSubtreeStream stream_invariant=new RewriteRuleSubtreeStream(adaptor,"rule invariant");
		RewriteRuleSubtreeStream stream_decreases=new RewriteRuleSubtreeStream(adaptor,"rule decreases");
		RewriteRuleSubtreeStream stream_ids=new RewriteRuleSubtreeStream(adaptor,"rule ids");
		RewriteRuleSubtreeStream stream_relaxedBlock=new RewriteRuleSubtreeStream(adaptor,"rule relaxedBlock");
		RewriteRuleSubtreeStream stream_expressions=new RewriteRuleSubtreeStream(adaptor,"rule expressions");

		try {
			// Dafny.g:171:10: ( ID ':=' ^ expression ';' !| ( ID ':=' 'call' )=>r= ID ':=' 'call' f= ID '(' ( expressions )? ')' ';' -> ^( 'call' $f ^( RESULTS $r) ^( ARGS ( expressions )? ) ) | ids ':=' 'call' ID '(' ( expressions )? ')' ';' -> ^( 'call' ID ^( RESULTS ids ) ^( ARGS ( expressions )? ) ) | ( 'label' ID ':' )? 'while' expression ( invariant )+ decreases relaxedBlock -> ^( 'while' ( ID )? expression ( invariant )+ decreases relaxedBlock ) | 'if' ^ expression relaxedBlock ( options {greedy=true; } : 'else' ! relaxedBlock )? | 'assert' ^ ( 'label' ! ID ':' !)? expression ';' !)
			int alt24=6;
			switch ( input.LA(1) ) {
			case ID:
				{
				int LA24_1 = input.LA(2);
				if ( (LA24_1==ASSIGN) ) {
					int LA24_5 = input.LA(3);
					if ( (LA24_5==CALL) && (synpred1_Dafny())) {
						alt24=2;
					}
					else if ( (LA24_5==BLOCK_BEGIN||LA24_5==ID||LA24_5==LIT||(LA24_5 >= MINUS && LA24_5 <= NOT)||LA24_5==53||LA24_5==58) ) {
						alt24=1;
					}

					else {
						if (state.backtracking>0) {state.failed=true; return retval;}
						int nvaeMark = input.mark();
						try {
							for (int nvaeConsume = 0; nvaeConsume < 3 - 1; nvaeConsume++) {
								input.consume();
							}
							NoViableAltException nvae =
								new NoViableAltException("", 24, 5, input);
							throw nvae;
						} finally {
							input.rewind(nvaeMark);
						}
					}

				}
				else if ( (LA24_1==55) ) {
					alt24=3;
				}

				else {
					if (state.backtracking>0) {state.failed=true; return retval;}
					int nvaeMark = input.mark();
					try {
						input.consume();
						NoViableAltException nvae =
							new NoViableAltException("", 24, 1, input);
						throw nvae;
					} finally {
						input.rewind(nvaeMark);
					}
				}

				}
				break;
			case LABEL:
			case WHILE:
				{
				alt24=4;
				}
				break;
			case IF:
				{
				alt24=5;
				}
				break;
			case ASSERT:
				{
				alt24=6;
				}
				break;
			default:
				if (state.backtracking>0) {state.failed=true; return retval;}
				NoViableAltException nvae =
					new NoViableAltException("", 24, 0, input);
				throw nvae;
			}
			switch (alt24) {
				case 1 :
					// Dafny.g:172:5: ID ':=' ^ expression ';' !
					{
					root_0 = (DafnyTree)adaptor.nil();


					ID59=(Token)match(input,ID,FOLLOW_ID_in_statement883); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					ID59_tree = (DafnyTree)adaptor.create(ID59);
					adaptor.addChild(root_0, ID59_tree);
					}

					string_literal60=(Token)match(input,ASSIGN,FOLLOW_ASSIGN_in_statement885); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					string_literal60_tree = (DafnyTree)adaptor.create(string_literal60);
					root_0 = (DafnyTree)adaptor.becomeRoot(string_literal60_tree, root_0);
					}

					pushFollow(FOLLOW_expression_in_statement888);
					expression61=expression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, expression61.getTree());

					char_literal62=(Token)match(input,57,FOLLOW_57_in_statement890); if (state.failed) return retval;
					}
					break;
				case 2 :
					// Dafny.g:173:5: ( ID ':=' 'call' )=>r= ID ':=' 'call' f= ID '(' ( expressions )? ')' ';'
					{
					r=(Token)match(input,ID,FOLLOW_ID_in_statement909); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_ID.add(r);

					string_literal63=(Token)match(input,ASSIGN,FOLLOW_ASSIGN_in_statement911); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_ASSIGN.add(string_literal63);

					string_literal64=(Token)match(input,CALL,FOLLOW_CALL_in_statement913); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_CALL.add(string_literal64);

					f=(Token)match(input,ID,FOLLOW_ID_in_statement917); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_ID.add(f);

					char_literal65=(Token)match(input,53,FOLLOW_53_in_statement919); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_53.add(char_literal65);

					// Dafny.g:173:51: ( expressions )?
					int alt18=2;
					int LA18_0 = input.LA(1);
					if ( (LA18_0==BLOCK_BEGIN||LA18_0==ID||LA18_0==LIT||(LA18_0 >= MINUS && LA18_0 <= NOT)||LA18_0==53||LA18_0==58) ) {
						alt18=1;
					}
					switch (alt18) {
						case 1 :
							// Dafny.g:173:51: expressions
							{
							pushFollow(FOLLOW_expressions_in_statement921);
							expressions66=expressions();
							state._fsp--;
							if (state.failed) return retval;
							if ( state.backtracking==0 ) stream_expressions.add(expressions66.getTree());
							}
							break;

					}

					char_literal67=(Token)match(input,54,FOLLOW_54_in_statement924); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_54.add(char_literal67);

					char_literal68=(Token)match(input,57,FOLLOW_57_in_statement926); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_57.add(char_literal68);

					// AST REWRITE
					// elements: expressions, f, r, CALL
					// token labels: f, r
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleTokenStream stream_f=new RewriteRuleTokenStream(adaptor,"token f",f);
					RewriteRuleTokenStream stream_r=new RewriteRuleTokenStream(adaptor,"token r",r);
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (DafnyTree)adaptor.nil();
					// 174:9: -> ^( 'call' $f ^( RESULTS $r) ^( ARGS ( expressions )? ) )
					{
						// Dafny.g:174:12: ^( 'call' $f ^( RESULTS $r) ^( ARGS ( expressions )? ) )
						{
						DafnyTree root_1 = (DafnyTree)adaptor.nil();
						root_1 = (DafnyTree)adaptor.becomeRoot(stream_CALL.nextNode(), root_1);
						adaptor.addChild(root_1, stream_f.nextNode());
						// Dafny.g:174:24: ^( RESULTS $r)
						{
						DafnyTree root_2 = (DafnyTree)adaptor.nil();
						root_2 = (DafnyTree)adaptor.becomeRoot((DafnyTree)adaptor.create(RESULTS, "RESULTS"), root_2);
						adaptor.addChild(root_2, stream_r.nextNode());
						adaptor.addChild(root_1, root_2);
						}

						// Dafny.g:174:38: ^( ARGS ( expressions )? )
						{
						DafnyTree root_2 = (DafnyTree)adaptor.nil();
						root_2 = (DafnyTree)adaptor.becomeRoot((DafnyTree)adaptor.create(ARGS, "ARGS"), root_2);
						// Dafny.g:174:45: ( expressions )?
						if ( stream_expressions.hasNext() ) {
							adaptor.addChild(root_2, stream_expressions.nextTree());
						}
						stream_expressions.reset();

						adaptor.addChild(root_1, root_2);
						}

						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;
				case 3 :
					// Dafny.g:175:5: ids ':=' 'call' ID '(' ( expressions )? ')' ';'
					{
					pushFollow(FOLLOW_ids_in_statement963);
					ids69=ids();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_ids.add(ids69.getTree());
					string_literal70=(Token)match(input,ASSIGN,FOLLOW_ASSIGN_in_statement965); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_ASSIGN.add(string_literal70);

					string_literal71=(Token)match(input,CALL,FOLLOW_CALL_in_statement967); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_CALL.add(string_literal71);

					ID72=(Token)match(input,ID,FOLLOW_ID_in_statement969); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_ID.add(ID72);

					char_literal73=(Token)match(input,53,FOLLOW_53_in_statement971); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_53.add(char_literal73);

					// Dafny.g:175:28: ( expressions )?
					int alt19=2;
					int LA19_0 = input.LA(1);
					if ( (LA19_0==BLOCK_BEGIN||LA19_0==ID||LA19_0==LIT||(LA19_0 >= MINUS && LA19_0 <= NOT)||LA19_0==53||LA19_0==58) ) {
						alt19=1;
					}
					switch (alt19) {
						case 1 :
							// Dafny.g:175:28: expressions
							{
							pushFollow(FOLLOW_expressions_in_statement973);
							expressions74=expressions();
							state._fsp--;
							if (state.failed) return retval;
							if ( state.backtracking==0 ) stream_expressions.add(expressions74.getTree());
							}
							break;

					}

					char_literal75=(Token)match(input,54,FOLLOW_54_in_statement976); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_54.add(char_literal75);

					char_literal76=(Token)match(input,57,FOLLOW_57_in_statement978); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_57.add(char_literal76);

					// AST REWRITE
					// elements: CALL, expressions, ids, ID
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (DafnyTree)adaptor.nil();
					// 176:9: -> ^( 'call' ID ^( RESULTS ids ) ^( ARGS ( expressions )? ) )
					{
						// Dafny.g:176:12: ^( 'call' ID ^( RESULTS ids ) ^( ARGS ( expressions )? ) )
						{
						DafnyTree root_1 = (DafnyTree)adaptor.nil();
						root_1 = (DafnyTree)adaptor.becomeRoot(stream_CALL.nextNode(), root_1);
						adaptor.addChild(root_1, stream_ID.nextNode());
						// Dafny.g:176:24: ^( RESULTS ids )
						{
						DafnyTree root_2 = (DafnyTree)adaptor.nil();
						root_2 = (DafnyTree)adaptor.becomeRoot((DafnyTree)adaptor.create(RESULTS, "RESULTS"), root_2);
						adaptor.addChild(root_2, stream_ids.nextTree());
						adaptor.addChild(root_1, root_2);
						}

						// Dafny.g:176:39: ^( ARGS ( expressions )? )
						{
						DafnyTree root_2 = (DafnyTree)adaptor.nil();
						root_2 = (DafnyTree)adaptor.becomeRoot((DafnyTree)adaptor.create(ARGS, "ARGS"), root_2);
						// Dafny.g:176:46: ( expressions )?
						if ( stream_expressions.hasNext() ) {
							adaptor.addChild(root_2, stream_expressions.nextTree());
						}
						stream_expressions.reset();

						adaptor.addChild(root_1, root_2);
						}

						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;
				case 4 :
					// Dafny.g:177:5: ( 'label' ID ':' )? 'while' expression ( invariant )+ decreases relaxedBlock
					{
					// Dafny.g:177:5: ( 'label' ID ':' )?
					int alt20=2;
					int LA20_0 = input.LA(1);
					if ( (LA20_0==LABEL) ) {
						alt20=1;
					}
					switch (alt20) {
						case 1 :
							// Dafny.g:177:6: 'label' ID ':'
							{
							string_literal77=(Token)match(input,LABEL,FOLLOW_LABEL_in_statement1014); if (state.failed) return retval; 
							if ( state.backtracking==0 ) stream_LABEL.add(string_literal77);

							ID78=(Token)match(input,ID,FOLLOW_ID_in_statement1016); if (state.failed) return retval; 
							if ( state.backtracking==0 ) stream_ID.add(ID78);

							char_literal79=(Token)match(input,56,FOLLOW_56_in_statement1018); if (state.failed) return retval; 
							if ( state.backtracking==0 ) stream_56.add(char_literal79);

							}
							break;

					}

					string_literal80=(Token)match(input,WHILE,FOLLOW_WHILE_in_statement1030); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_WHILE.add(string_literal80);

					pushFollow(FOLLOW_expression_in_statement1032);
					expression81=expression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_expression.add(expression81.getTree());
					// Dafny.g:178:26: ( invariant )+
					int cnt21=0;
					loop21:
					while (true) {
						int alt21=2;
						int LA21_0 = input.LA(1);
						if ( (LA21_0==INVARIANT) ) {
							alt21=1;
						}

						switch (alt21) {
						case 1 :
							// Dafny.g:178:26: invariant
							{
							pushFollow(FOLLOW_invariant_in_statement1034);
							invariant82=invariant();
							state._fsp--;
							if (state.failed) return retval;
							if ( state.backtracking==0 ) stream_invariant.add(invariant82.getTree());
							}
							break;

						default :
							if ( cnt21 >= 1 ) break loop21;
							if (state.backtracking>0) {state.failed=true; return retval;}
							EarlyExitException eee = new EarlyExitException(21, input);
							throw eee;
						}
						cnt21++;
					}

					pushFollow(FOLLOW_decreases_in_statement1037);
					decreases83=decreases();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_decreases.add(decreases83.getTree());
					pushFollow(FOLLOW_relaxedBlock_in_statement1039);
					relaxedBlock84=relaxedBlock();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_relaxedBlock.add(relaxedBlock84.getTree());
					// AST REWRITE
					// elements: WHILE, relaxedBlock, expression, decreases, invariant, ID
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (DafnyTree)adaptor.nil();
					// 179:9: -> ^( 'while' ( ID )? expression ( invariant )+ decreases relaxedBlock )
					{
						// Dafny.g:179:12: ^( 'while' ( ID )? expression ( invariant )+ decreases relaxedBlock )
						{
						DafnyTree root_1 = (DafnyTree)adaptor.nil();
						root_1 = (DafnyTree)adaptor.becomeRoot(stream_WHILE.nextNode(), root_1);
						// Dafny.g:179:22: ( ID )?
						if ( stream_ID.hasNext() ) {
							adaptor.addChild(root_1, stream_ID.nextNode());
						}
						stream_ID.reset();

						adaptor.addChild(root_1, stream_expression.nextTree());
						if ( !(stream_invariant.hasNext()) ) {
							throw new RewriteEarlyExitException();
						}
						while ( stream_invariant.hasNext() ) {
							adaptor.addChild(root_1, stream_invariant.nextTree());
						}
						stream_invariant.reset();

						adaptor.addChild(root_1, stream_decreases.nextTree());
						adaptor.addChild(root_1, stream_relaxedBlock.nextTree());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;
				case 5 :
					// Dafny.g:180:5: 'if' ^ expression relaxedBlock ( options {greedy=true; } : 'else' ! relaxedBlock )?
					{
					root_0 = (DafnyTree)adaptor.nil();


					string_literal85=(Token)match(input,IF,FOLLOW_IF_in_statement1071); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					string_literal85_tree = (DafnyTree)adaptor.create(string_literal85);
					root_0 = (DafnyTree)adaptor.becomeRoot(string_literal85_tree, root_0);
					}

					pushFollow(FOLLOW_expression_in_statement1074);
					expression86=expression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, expression86.getTree());

					pushFollow(FOLLOW_relaxedBlock_in_statement1076);
					relaxedBlock87=relaxedBlock();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, relaxedBlock87.getTree());

					// Dafny.g:181:7: ( options {greedy=true; } : 'else' ! relaxedBlock )?
					int alt22=2;
					int LA22_0 = input.LA(1);
					if ( (LA22_0==ELSE) ) {
						alt22=1;
					}
					switch (alt22) {
						case 1 :
							// Dafny.g:181:36: 'else' ! relaxedBlock
							{
							string_literal88=(Token)match(input,ELSE,FOLLOW_ELSE_in_statement1097); if (state.failed) return retval;
							pushFollow(FOLLOW_relaxedBlock_in_statement1100);
							relaxedBlock89=relaxedBlock();
							state._fsp--;
							if (state.failed) return retval;
							if ( state.backtracking==0 ) adaptor.addChild(root_0, relaxedBlock89.getTree());

							}
							break;

					}

					}
					break;
				case 6 :
					// Dafny.g:182:5: 'assert' ^ ( 'label' ! ID ':' !)? expression ';' !
					{
					root_0 = (DafnyTree)adaptor.nil();


					string_literal90=(Token)match(input,ASSERT,FOLLOW_ASSERT_in_statement1109); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					string_literal90_tree = (DafnyTree)adaptor.create(string_literal90);
					root_0 = (DafnyTree)adaptor.becomeRoot(string_literal90_tree, root_0);
					}

					// Dafny.g:182:15: ( 'label' ! ID ':' !)?
					int alt23=2;
					int LA23_0 = input.LA(1);
					if ( (LA23_0==LABEL) ) {
						alt23=1;
					}
					switch (alt23) {
						case 1 :
							// Dafny.g:182:17: 'label' ! ID ':' !
							{
							string_literal91=(Token)match(input,LABEL,FOLLOW_LABEL_in_statement1114); if (state.failed) return retval;
							ID92=(Token)match(input,ID,FOLLOW_ID_in_statement1117); if (state.failed) return retval;
							if ( state.backtracking==0 ) {
							ID92_tree = (DafnyTree)adaptor.create(ID92);
							adaptor.addChild(root_0, ID92_tree);
							}

							char_literal93=(Token)match(input,56,FOLLOW_56_in_statement1119); if (state.failed) return retval;
							}
							break;

					}

					pushFollow(FOLLOW_expression_in_statement1125);
					expression94=expression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, expression94.getTree());

					char_literal95=(Token)match(input,57,FOLLOW_57_in_statement1127); if (state.failed) return retval;
					}
					break;

			}
			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (DafnyTree)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
		}

		  catch (RecognitionException e) {
		    throw e;
		  }

		finally {
			// do for sure before leaving
		}
		return retval;
	}
	// $ANTLR end "statement"


	public static class ids_return extends ParserRuleReturnScope {
		DafnyTree tree;
		@Override
		public DafnyTree getTree() { return tree; }
	};


	// $ANTLR start "ids"
	// Dafny.g:185:1: ids : ID ( ',' ! ID )+ ;
	public final DafnyParser.ids_return ids() throws RecognitionException {
		DafnyParser.ids_return retval = new DafnyParser.ids_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		Token ID96=null;
		Token char_literal97=null;
		Token ID98=null;

		DafnyTree ID96_tree=null;
		DafnyTree char_literal97_tree=null;
		DafnyTree ID98_tree=null;

		try {
			// Dafny.g:185:4: ( ID ( ',' ! ID )+ )
			// Dafny.g:186:3: ID ( ',' ! ID )+
			{
			root_0 = (DafnyTree)adaptor.nil();


			ID96=(Token)match(input,ID,FOLLOW_ID_in_ids1140); if (state.failed) return retval;
			if ( state.backtracking==0 ) {
			ID96_tree = (DafnyTree)adaptor.create(ID96);
			adaptor.addChild(root_0, ID96_tree);
			}

			// Dafny.g:186:6: ( ',' ! ID )+
			int cnt25=0;
			loop25:
			while (true) {
				int alt25=2;
				int LA25_0 = input.LA(1);
				if ( (LA25_0==55) ) {
					alt25=1;
				}

				switch (alt25) {
				case 1 :
					// Dafny.g:186:7: ',' ! ID
					{
					char_literal97=(Token)match(input,55,FOLLOW_55_in_ids1143); if (state.failed) return retval;
					ID98=(Token)match(input,ID,FOLLOW_ID_in_ids1146); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					ID98_tree = (DafnyTree)adaptor.create(ID98);
					adaptor.addChild(root_0, ID98_tree);
					}

					}
					break;

				default :
					if ( cnt25 >= 1 ) break loop25;
					if (state.backtracking>0) {state.failed=true; return retval;}
					EarlyExitException eee = new EarlyExitException(25, input);
					throw eee;
				}
				cnt25++;
			}

			}

			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (DafnyTree)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
		}

		  catch (RecognitionException e) {
		    throw e;
		  }

		finally {
			// do for sure before leaving
		}
		return retval;
	}
	// $ANTLR end "ids"


	public static class expressions_return extends ParserRuleReturnScope {
		DafnyTree tree;
		@Override
		public DafnyTree getTree() { return tree; }
	};


	// $ANTLR start "expressions"
	// Dafny.g:189:1: expressions : expression ( ',' ! expression )* ;
	public final DafnyParser.expressions_return expressions() throws RecognitionException {
		DafnyParser.expressions_return retval = new DafnyParser.expressions_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		Token char_literal100=null;
		ParserRuleReturnScope expression99 =null;
		ParserRuleReturnScope expression101 =null;

		DafnyTree char_literal100_tree=null;

		try {
			// Dafny.g:189:12: ( expression ( ',' ! expression )* )
			// Dafny.g:190:3: expression ( ',' ! expression )*
			{
			root_0 = (DafnyTree)adaptor.nil();


			pushFollow(FOLLOW_expression_in_expressions1160);
			expression99=expression();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, expression99.getTree());

			// Dafny.g:190:14: ( ',' ! expression )*
			loop26:
			while (true) {
				int alt26=2;
				int LA26_0 = input.LA(1);
				if ( (LA26_0==55) ) {
					alt26=1;
				}

				switch (alt26) {
				case 1 :
					// Dafny.g:190:16: ',' ! expression
					{
					char_literal100=(Token)match(input,55,FOLLOW_55_in_expressions1164); if (state.failed) return retval;
					pushFollow(FOLLOW_expression_in_expressions1167);
					expression101=expression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, expression101.getTree());

					}
					break;

				default :
					break loop26;
				}
			}

			}

			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (DafnyTree)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
		}

		  catch (RecognitionException e) {
		    throw e;
		  }

		finally {
			// do for sure before leaving
		}
		return retval;
	}
	// $ANTLR end "expressions"


	public static class expression_return extends ParserRuleReturnScope {
		DafnyTree tree;
		@Override
		public DafnyTree getTree() { return tree; }
	};


	// $ANTLR start "expression"
	// Dafny.g:193:1: expression : or_expr ;
	public final DafnyParser.expression_return expression() throws RecognitionException {
		DafnyParser.expression_return retval = new DafnyParser.expression_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		ParserRuleReturnScope or_expr102 =null;


		try {
			// Dafny.g:193:11: ( or_expr )
			// Dafny.g:194:3: or_expr
			{
			root_0 = (DafnyTree)adaptor.nil();


			pushFollow(FOLLOW_or_expr_in_expression1182);
			or_expr102=or_expr();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, or_expr102.getTree());

			}

			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (DafnyTree)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
		}

		  catch (RecognitionException e) {
		    throw e;
		  }

		finally {
			// do for sure before leaving
		}
		return retval;
	}
	// $ANTLR end "expression"


	public static class or_expr_return extends ParserRuleReturnScope {
		DafnyTree tree;
		@Override
		public DafnyTree getTree() { return tree; }
	};


	// $ANTLR start "or_expr"
	// Dafny.g:196:1: or_expr : and_expr ( ( '||' ^| '==>' ^) or_expr )? ;
	public final DafnyParser.or_expr_return or_expr() throws RecognitionException {
		DafnyParser.or_expr_return retval = new DafnyParser.or_expr_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		Token string_literal104=null;
		Token string_literal105=null;
		ParserRuleReturnScope and_expr103 =null;
		ParserRuleReturnScope or_expr106 =null;

		DafnyTree string_literal104_tree=null;
		DafnyTree string_literal105_tree=null;

		try {
			// Dafny.g:196:8: ( and_expr ( ( '||' ^| '==>' ^) or_expr )? )
			// Dafny.g:197:3: and_expr ( ( '||' ^| '==>' ^) or_expr )?
			{
			root_0 = (DafnyTree)adaptor.nil();


			pushFollow(FOLLOW_and_expr_in_or_expr1191);
			and_expr103=and_expr();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, and_expr103.getTree());

			// Dafny.g:197:12: ( ( '||' ^| '==>' ^) or_expr )?
			int alt28=2;
			int LA28_0 = input.LA(1);
			if ( (LA28_0==IMPLIES||LA28_0==OR) ) {
				alt28=1;
			}
			switch (alt28) {
				case 1 :
					// Dafny.g:197:14: ( '||' ^| '==>' ^) or_expr
					{
					// Dafny.g:197:14: ( '||' ^| '==>' ^)
					int alt27=2;
					int LA27_0 = input.LA(1);
					if ( (LA27_0==OR) ) {
						alt27=1;
					}
					else if ( (LA27_0==IMPLIES) ) {
						alt27=2;
					}

					else {
						if (state.backtracking>0) {state.failed=true; return retval;}
						NoViableAltException nvae =
							new NoViableAltException("", 27, 0, input);
						throw nvae;
					}

					switch (alt27) {
						case 1 :
							// Dafny.g:197:15: '||' ^
							{
							string_literal104=(Token)match(input,OR,FOLLOW_OR_in_or_expr1196); if (state.failed) return retval;
							if ( state.backtracking==0 ) {
							string_literal104_tree = (DafnyTree)adaptor.create(string_literal104);
							root_0 = (DafnyTree)adaptor.becomeRoot(string_literal104_tree, root_0);
							}

							}
							break;
						case 2 :
							// Dafny.g:197:23: '==>' ^
							{
							string_literal105=(Token)match(input,IMPLIES,FOLLOW_IMPLIES_in_or_expr1201); if (state.failed) return retval;
							if ( state.backtracking==0 ) {
							string_literal105_tree = (DafnyTree)adaptor.create(string_literal105);
							root_0 = (DafnyTree)adaptor.becomeRoot(string_literal105_tree, root_0);
							}

							}
							break;

					}

					pushFollow(FOLLOW_or_expr_in_or_expr1205);
					or_expr106=or_expr();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, or_expr106.getTree());

					}
					break;

			}

			}

			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (DafnyTree)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
		}

		  catch (RecognitionException e) {
		    throw e;
		  }

		finally {
			// do for sure before leaving
		}
		return retval;
	}
	// $ANTLR end "or_expr"


	public static class and_expr_return extends ParserRuleReturnScope {
		DafnyTree tree;
		@Override
		public DafnyTree getTree() { return tree; }
	};


	// $ANTLR start "and_expr"
	// Dafny.g:200:1: and_expr : rel_expr ( '&&' ^ and_expr )? ;
	public final DafnyParser.and_expr_return and_expr() throws RecognitionException {
		DafnyParser.and_expr_return retval = new DafnyParser.and_expr_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		Token string_literal108=null;
		ParserRuleReturnScope rel_expr107 =null;
		ParserRuleReturnScope and_expr109 =null;

		DafnyTree string_literal108_tree=null;

		try {
			// Dafny.g:200:9: ( rel_expr ( '&&' ^ and_expr )? )
			// Dafny.g:201:3: rel_expr ( '&&' ^ and_expr )?
			{
			root_0 = (DafnyTree)adaptor.nil();


			pushFollow(FOLLOW_rel_expr_in_and_expr1220);
			rel_expr107=rel_expr();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, rel_expr107.getTree());

			// Dafny.g:201:12: ( '&&' ^ and_expr )?
			int alt29=2;
			int LA29_0 = input.LA(1);
			if ( (LA29_0==AND) ) {
				alt29=1;
			}
			switch (alt29) {
				case 1 :
					// Dafny.g:201:14: '&&' ^ and_expr
					{
					string_literal108=(Token)match(input,AND,FOLLOW_AND_in_and_expr1224); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					string_literal108_tree = (DafnyTree)adaptor.create(string_literal108);
					root_0 = (DafnyTree)adaptor.becomeRoot(string_literal108_tree, root_0);
					}

					pushFollow(FOLLOW_and_expr_in_and_expr1227);
					and_expr109=and_expr();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, and_expr109.getTree());

					}
					break;

			}

			}

			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (DafnyTree)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
		}

		  catch (RecognitionException e) {
		    throw e;
		  }

		finally {
			// do for sure before leaving
		}
		return retval;
	}
	// $ANTLR end "and_expr"


	public static class rel_expr_return extends ParserRuleReturnScope {
		DafnyTree tree;
		@Override
		public DafnyTree getTree() { return tree; }
	};


	// $ANTLR start "rel_expr"
	// Dafny.g:204:1: rel_expr : add_expr ( ( '<' ^| '>' ^| '==' ^| '<=' ^| '>=' ^) add_expr )? ;
	public final DafnyParser.rel_expr_return rel_expr() throws RecognitionException {
		DafnyParser.rel_expr_return retval = new DafnyParser.rel_expr_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		Token char_literal111=null;
		Token char_literal112=null;
		Token string_literal113=null;
		Token string_literal114=null;
		Token string_literal115=null;
		ParserRuleReturnScope add_expr110 =null;
		ParserRuleReturnScope add_expr116 =null;

		DafnyTree char_literal111_tree=null;
		DafnyTree char_literal112_tree=null;
		DafnyTree string_literal113_tree=null;
		DafnyTree string_literal114_tree=null;
		DafnyTree string_literal115_tree=null;

		try {
			// Dafny.g:204:9: ( add_expr ( ( '<' ^| '>' ^| '==' ^| '<=' ^| '>=' ^) add_expr )? )
			// Dafny.g:205:3: add_expr ( ( '<' ^| '>' ^| '==' ^| '<=' ^| '>=' ^) add_expr )?
			{
			root_0 = (DafnyTree)adaptor.nil();


			pushFollow(FOLLOW_add_expr_in_rel_expr1242);
			add_expr110=add_expr();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, add_expr110.getTree());

			// Dafny.g:205:12: ( ( '<' ^| '>' ^| '==' ^| '<=' ^| '>=' ^) add_expr )?
			int alt31=2;
			int LA31_0 = input.LA(1);
			if ( (LA31_0==EQ||(LA31_0 >= GE && LA31_0 <= GT)||LA31_0==LE||LA31_0==LT) ) {
				alt31=1;
			}
			switch (alt31) {
				case 1 :
					// Dafny.g:205:14: ( '<' ^| '>' ^| '==' ^| '<=' ^| '>=' ^) add_expr
					{
					// Dafny.g:205:14: ( '<' ^| '>' ^| '==' ^| '<=' ^| '>=' ^)
					int alt30=5;
					switch ( input.LA(1) ) {
					case LT:
						{
						alt30=1;
						}
						break;
					case GT:
						{
						alt30=2;
						}
						break;
					case EQ:
						{
						alt30=3;
						}
						break;
					case LE:
						{
						alt30=4;
						}
						break;
					case GE:
						{
						alt30=5;
						}
						break;
					default:
						if (state.backtracking>0) {state.failed=true; return retval;}
						NoViableAltException nvae =
							new NoViableAltException("", 30, 0, input);
						throw nvae;
					}
					switch (alt30) {
						case 1 :
							// Dafny.g:205:15: '<' ^
							{
							char_literal111=(Token)match(input,LT,FOLLOW_LT_in_rel_expr1247); if (state.failed) return retval;
							if ( state.backtracking==0 ) {
							char_literal111_tree = (DafnyTree)adaptor.create(char_literal111);
							root_0 = (DafnyTree)adaptor.becomeRoot(char_literal111_tree, root_0);
							}

							}
							break;
						case 2 :
							// Dafny.g:205:22: '>' ^
							{
							char_literal112=(Token)match(input,GT,FOLLOW_GT_in_rel_expr1252); if (state.failed) return retval;
							if ( state.backtracking==0 ) {
							char_literal112_tree = (DafnyTree)adaptor.create(char_literal112);
							root_0 = (DafnyTree)adaptor.becomeRoot(char_literal112_tree, root_0);
							}

							}
							break;
						case 3 :
							// Dafny.g:205:29: '==' ^
							{
							string_literal113=(Token)match(input,EQ,FOLLOW_EQ_in_rel_expr1257); if (state.failed) return retval;
							if ( state.backtracking==0 ) {
							string_literal113_tree = (DafnyTree)adaptor.create(string_literal113);
							root_0 = (DafnyTree)adaptor.becomeRoot(string_literal113_tree, root_0);
							}

							}
							break;
						case 4 :
							// Dafny.g:205:37: '<=' ^
							{
							string_literal114=(Token)match(input,LE,FOLLOW_LE_in_rel_expr1262); if (state.failed) return retval;
							if ( state.backtracking==0 ) {
							string_literal114_tree = (DafnyTree)adaptor.create(string_literal114);
							root_0 = (DafnyTree)adaptor.becomeRoot(string_literal114_tree, root_0);
							}

							}
							break;
						case 5 :
							// Dafny.g:205:45: '>=' ^
							{
							string_literal115=(Token)match(input,GE,FOLLOW_GE_in_rel_expr1267); if (state.failed) return retval;
							if ( state.backtracking==0 ) {
							string_literal115_tree = (DafnyTree)adaptor.create(string_literal115);
							root_0 = (DafnyTree)adaptor.becomeRoot(string_literal115_tree, root_0);
							}

							}
							break;

					}

					pushFollow(FOLLOW_add_expr_in_rel_expr1271);
					add_expr116=add_expr();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, add_expr116.getTree());

					}
					break;

			}

			}

			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (DafnyTree)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
		}

		  catch (RecognitionException e) {
		    throw e;
		  }

		finally {
			// do for sure before leaving
		}
		return retval;
	}
	// $ANTLR end "rel_expr"


	public static class add_expr_return extends ParserRuleReturnScope {
		DafnyTree tree;
		@Override
		public DafnyTree getTree() { return tree; }
	};


	// $ANTLR start "add_expr"
	// Dafny.g:208:1: add_expr : mul_expr ( ( '+' | '-' | '++' ) ^ add_expr )? ;
	public final DafnyParser.add_expr_return add_expr() throws RecognitionException {
		DafnyParser.add_expr_return retval = new DafnyParser.add_expr_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		Token set118=null;
		ParserRuleReturnScope mul_expr117 =null;
		ParserRuleReturnScope add_expr119 =null;

		DafnyTree set118_tree=null;

		try {
			// Dafny.g:208:9: ( mul_expr ( ( '+' | '-' | '++' ) ^ add_expr )? )
			// Dafny.g:209:3: mul_expr ( ( '+' | '-' | '++' ) ^ add_expr )?
			{
			root_0 = (DafnyTree)adaptor.nil();


			pushFollow(FOLLOW_mul_expr_in_add_expr1286);
			mul_expr117=mul_expr();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, mul_expr117.getTree());

			// Dafny.g:209:12: ( ( '+' | '-' | '++' ) ^ add_expr )?
			int alt32=2;
			int LA32_0 = input.LA(1);
			if ( (LA32_0==MINUS||LA32_0==PLUS||LA32_0==UNION) ) {
				alt32=1;
			}
			switch (alt32) {
				case 1 :
					// Dafny.g:209:14: ( '+' | '-' | '++' ) ^ add_expr
					{
					set118=input.LT(1);
					set118=input.LT(1);
					if ( input.LA(1)==MINUS||input.LA(1)==PLUS||input.LA(1)==UNION ) {
						input.consume();
						if ( state.backtracking==0 ) root_0 = (DafnyTree)adaptor.becomeRoot((DafnyTree)adaptor.create(set118), root_0);
						state.errorRecovery=false;
						state.failed=false;
					}
					else {
						if (state.backtracking>0) {state.failed=true; return retval;}
						MismatchedSetException mse = new MismatchedSetException(null,input);
						throw mse;
					}
					pushFollow(FOLLOW_add_expr_in_add_expr1303);
					add_expr119=add_expr();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, add_expr119.getTree());

					}
					break;

			}

			}

			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (DafnyTree)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
		}

		  catch (RecognitionException e) {
		    throw e;
		  }

		finally {
			// do for sure before leaving
		}
		return retval;
	}
	// $ANTLR end "add_expr"


	public static class mul_expr_return extends ParserRuleReturnScope {
		DafnyTree tree;
		@Override
		public DafnyTree getTree() { return tree; }
	};


	// $ANTLR start "mul_expr"
	// Dafny.g:212:1: mul_expr : prefix_expr ( ( '*' | '**' ) ^ mul_expr )? ;
	public final DafnyParser.mul_expr_return mul_expr() throws RecognitionException {
		DafnyParser.mul_expr_return retval = new DafnyParser.mul_expr_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		Token set121=null;
		ParserRuleReturnScope prefix_expr120 =null;
		ParserRuleReturnScope mul_expr122 =null;

		DafnyTree set121_tree=null;

		try {
			// Dafny.g:212:9: ( prefix_expr ( ( '*' | '**' ) ^ mul_expr )? )
			// Dafny.g:213:3: prefix_expr ( ( '*' | '**' ) ^ mul_expr )?
			{
			root_0 = (DafnyTree)adaptor.nil();


			pushFollow(FOLLOW_prefix_expr_in_mul_expr1318);
			prefix_expr120=prefix_expr();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, prefix_expr120.getTree());

			// Dafny.g:213:15: ( ( '*' | '**' ) ^ mul_expr )?
			int alt33=2;
			int LA33_0 = input.LA(1);
			if ( (LA33_0==INTERSECT||LA33_0==TIMES) ) {
				alt33=1;
			}
			switch (alt33) {
				case 1 :
					// Dafny.g:213:17: ( '*' | '**' ) ^ mul_expr
					{
					set121=input.LT(1);
					set121=input.LT(1);
					if ( input.LA(1)==INTERSECT||input.LA(1)==TIMES ) {
						input.consume();
						if ( state.backtracking==0 ) root_0 = (DafnyTree)adaptor.becomeRoot((DafnyTree)adaptor.create(set121), root_0);
						state.errorRecovery=false;
						state.failed=false;
					}
					else {
						if (state.backtracking>0) {state.failed=true; return retval;}
						MismatchedSetException mse = new MismatchedSetException(null,input);
						throw mse;
					}
					pushFollow(FOLLOW_mul_expr_in_mul_expr1331);
					mul_expr122=mul_expr();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, mul_expr122.getTree());

					}
					break;

			}

			}

			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (DafnyTree)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
		}

		  catch (RecognitionException e) {
		    throw e;
		  }

		finally {
			// do for sure before leaving
		}
		return retval;
	}
	// $ANTLR end "mul_expr"


	public static class prefix_expr_return extends ParserRuleReturnScope {
		DafnyTree tree;
		@Override
		public DafnyTree getTree() { return tree; }
	};


	// $ANTLR start "prefix_expr"
	// Dafny.g:216:1: prefix_expr : ( '-' ^ prefix_expr | '!' ^ prefix_expr | postfix_expr );
	public final DafnyParser.prefix_expr_return prefix_expr() throws RecognitionException {
		DafnyParser.prefix_expr_return retval = new DafnyParser.prefix_expr_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		Token char_literal123=null;
		Token char_literal125=null;
		ParserRuleReturnScope prefix_expr124 =null;
		ParserRuleReturnScope prefix_expr126 =null;
		ParserRuleReturnScope postfix_expr127 =null;

		DafnyTree char_literal123_tree=null;
		DafnyTree char_literal125_tree=null;

		try {
			// Dafny.g:216:12: ( '-' ^ prefix_expr | '!' ^ prefix_expr | postfix_expr )
			int alt34=3;
			switch ( input.LA(1) ) {
			case MINUS:
				{
				alt34=1;
				}
				break;
			case NOT:
				{
				alt34=2;
				}
				break;
			case BLOCK_BEGIN:
			case ID:
			case LIT:
			case 53:
			case 58:
				{
				alt34=3;
				}
				break;
			default:
				if (state.backtracking>0) {state.failed=true; return retval;}
				NoViableAltException nvae =
					new NoViableAltException("", 34, 0, input);
				throw nvae;
			}
			switch (alt34) {
				case 1 :
					// Dafny.g:217:5: '-' ^ prefix_expr
					{
					root_0 = (DafnyTree)adaptor.nil();


					char_literal123=(Token)match(input,MINUS,FOLLOW_MINUS_in_prefix_expr1348); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					char_literal123_tree = (DafnyTree)adaptor.create(char_literal123);
					root_0 = (DafnyTree)adaptor.becomeRoot(char_literal123_tree, root_0);
					}

					pushFollow(FOLLOW_prefix_expr_in_prefix_expr1351);
					prefix_expr124=prefix_expr();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, prefix_expr124.getTree());

					}
					break;
				case 2 :
					// Dafny.g:218:5: '!' ^ prefix_expr
					{
					root_0 = (DafnyTree)adaptor.nil();


					char_literal125=(Token)match(input,NOT,FOLLOW_NOT_in_prefix_expr1357); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					char_literal125_tree = (DafnyTree)adaptor.create(char_literal125);
					root_0 = (DafnyTree)adaptor.becomeRoot(char_literal125_tree, root_0);
					}

					pushFollow(FOLLOW_prefix_expr_in_prefix_expr1360);
					prefix_expr126=prefix_expr();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, prefix_expr126.getTree());

					}
					break;
				case 3 :
					// Dafny.g:219:5: postfix_expr
					{
					root_0 = (DafnyTree)adaptor.nil();


					pushFollow(FOLLOW_postfix_expr_in_prefix_expr1366);
					postfix_expr127=postfix_expr();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, postfix_expr127.getTree());

					}
					break;

			}
			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (DafnyTree)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
		}

		  catch (RecognitionException e) {
		    throw e;
		  }

		finally {
			// do for sure before leaving
		}
		return retval;
	}
	// $ANTLR end "prefix_expr"


	public static class postfix_expr_return extends ParserRuleReturnScope {
		DafnyTree tree;
		@Override
		public DafnyTree getTree() { return tree; }
	};


	// $ANTLR start "postfix_expr"
	// Dafny.g:222:1: postfix_expr : atom_expr ( '[' expression ']' -> ^( ARRAY_ACCESS atom_expr expression ) | '.' LENGTH -> ^( LENGTH atom_expr ) | -> atom_expr ) ;
	public final DafnyParser.postfix_expr_return postfix_expr() throws RecognitionException {
		DafnyParser.postfix_expr_return retval = new DafnyParser.postfix_expr_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		Token char_literal129=null;
		Token char_literal131=null;
		Token char_literal132=null;
		Token LENGTH133=null;
		ParserRuleReturnScope atom_expr128 =null;
		ParserRuleReturnScope expression130 =null;

		DafnyTree char_literal129_tree=null;
		DafnyTree char_literal131_tree=null;
		DafnyTree char_literal132_tree=null;
		DafnyTree LENGTH133_tree=null;
		RewriteRuleTokenStream stream_59=new RewriteRuleTokenStream(adaptor,"token 59");
		RewriteRuleTokenStream stream_58=new RewriteRuleTokenStream(adaptor,"token 58");
		RewriteRuleTokenStream stream_DOT=new RewriteRuleTokenStream(adaptor,"token DOT");
		RewriteRuleTokenStream stream_LENGTH=new RewriteRuleTokenStream(adaptor,"token LENGTH");
		RewriteRuleSubtreeStream stream_expression=new RewriteRuleSubtreeStream(adaptor,"rule expression");
		RewriteRuleSubtreeStream stream_atom_expr=new RewriteRuleSubtreeStream(adaptor,"rule atom_expr");

		try {
			// Dafny.g:222:13: ( atom_expr ( '[' expression ']' -> ^( ARRAY_ACCESS atom_expr expression ) | '.' LENGTH -> ^( LENGTH atom_expr ) | -> atom_expr ) )
			// Dafny.g:223:3: atom_expr ( '[' expression ']' -> ^( ARRAY_ACCESS atom_expr expression ) | '.' LENGTH -> ^( LENGTH atom_expr ) | -> atom_expr )
			{
			pushFollow(FOLLOW_atom_expr_in_postfix_expr1378);
			atom_expr128=atom_expr();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) stream_atom_expr.add(atom_expr128.getTree());
			// Dafny.g:224:3: ( '[' expression ']' -> ^( ARRAY_ACCESS atom_expr expression ) | '.' LENGTH -> ^( LENGTH atom_expr ) | -> atom_expr )
			int alt35=3;
			switch ( input.LA(1) ) {
			case 58:
				{
				alt35=1;
				}
				break;
			case DOT:
				{
				alt35=2;
				}
				break;
			case AND:
			case ASSERT:
			case BLOCK_BEGIN:
			case BLOCK_END:
			case DECREASES:
			case ENSURES:
			case EQ:
			case GE:
			case GT:
			case ID:
			case IF:
			case IMPLIES:
			case INTERSECT:
			case INVARIANT:
			case LABEL:
			case LE:
			case LT:
			case MINUS:
			case OR:
			case PLUS:
			case REQUIRES:
			case TIMES:
			case UNION:
			case WHILE:
			case 54:
			case 55:
			case 57:
			case 59:
				{
				alt35=3;
				}
				break;
			default:
				if (state.backtracking>0) {state.failed=true; return retval;}
				NoViableAltException nvae =
					new NoViableAltException("", 35, 0, input);
				throw nvae;
			}
			switch (alt35) {
				case 1 :
					// Dafny.g:224:5: '[' expression ']'
					{
					char_literal129=(Token)match(input,58,FOLLOW_58_in_postfix_expr1384); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_58.add(char_literal129);

					pushFollow(FOLLOW_expression_in_postfix_expr1386);
					expression130=expression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_expression.add(expression130.getTree());
					char_literal131=(Token)match(input,59,FOLLOW_59_in_postfix_expr1388); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_59.add(char_literal131);

					// AST REWRITE
					// elements: expression, atom_expr
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (DafnyTree)adaptor.nil();
					// 224:24: -> ^( ARRAY_ACCESS atom_expr expression )
					{
						// Dafny.g:224:27: ^( ARRAY_ACCESS atom_expr expression )
						{
						DafnyTree root_1 = (DafnyTree)adaptor.nil();
						root_1 = (DafnyTree)adaptor.becomeRoot((DafnyTree)adaptor.create(ARRAY_ACCESS, "ARRAY_ACCESS"), root_1);
						adaptor.addChild(root_1, stream_atom_expr.nextTree());
						adaptor.addChild(root_1, stream_expression.nextTree());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;
				case 2 :
					// Dafny.g:225:5: '.' LENGTH
					{
					char_literal132=(Token)match(input,DOT,FOLLOW_DOT_in_postfix_expr1406); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_DOT.add(char_literal132);

					LENGTH133=(Token)match(input,LENGTH,FOLLOW_LENGTH_in_postfix_expr1408); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_LENGTH.add(LENGTH133);

					// AST REWRITE
					// elements: atom_expr, LENGTH
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (DafnyTree)adaptor.nil();
					// 225:16: -> ^( LENGTH atom_expr )
					{
						// Dafny.g:225:19: ^( LENGTH atom_expr )
						{
						DafnyTree root_1 = (DafnyTree)adaptor.nil();
						root_1 = (DafnyTree)adaptor.becomeRoot(stream_LENGTH.nextNode(), root_1);
						adaptor.addChild(root_1, stream_atom_expr.nextTree());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;
				case 3 :
					// Dafny.g:226:5: 
					{
					// AST REWRITE
					// elements: atom_expr
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (DafnyTree)adaptor.nil();
					// 226:5: -> atom_expr
					{
						adaptor.addChild(root_0, stream_atom_expr.nextTree());
					}


					retval.tree = root_0;
					}

					}
					break;

			}

			}

			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (DafnyTree)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
		}

		  catch (RecognitionException e) {
		    throw e;
		  }

		finally {
			// do for sure before leaving
		}
		return retval;
	}
	// $ANTLR end "postfix_expr"


	public static class atom_expr_return extends ParserRuleReturnScope {
		DafnyTree tree;
		@Override
		public DafnyTree getTree() { return tree; }
	};


	// $ANTLR start "atom_expr"
	// Dafny.g:230:1: atom_expr : ( ID | LIT | quantifier | '(' ! expression ')' !| '{' ( expressions )? '}' -> ^( SETEX ( expressions )? ) | '[' ( expressions )? ']' -> ^( LISTEX ( expressions )? ) );
	public final DafnyParser.atom_expr_return atom_expr() throws RecognitionException {
		DafnyParser.atom_expr_return retval = new DafnyParser.atom_expr_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		Token ID134=null;
		Token LIT135=null;
		Token char_literal137=null;
		Token char_literal139=null;
		Token char_literal140=null;
		Token char_literal142=null;
		Token char_literal143=null;
		Token char_literal145=null;
		ParserRuleReturnScope quantifier136 =null;
		ParserRuleReturnScope expression138 =null;
		ParserRuleReturnScope expressions141 =null;
		ParserRuleReturnScope expressions144 =null;

		DafnyTree ID134_tree=null;
		DafnyTree LIT135_tree=null;
		DafnyTree char_literal137_tree=null;
		DafnyTree char_literal139_tree=null;
		DafnyTree char_literal140_tree=null;
		DafnyTree char_literal142_tree=null;
		DafnyTree char_literal143_tree=null;
		DafnyTree char_literal145_tree=null;
		RewriteRuleTokenStream stream_59=new RewriteRuleTokenStream(adaptor,"token 59");
		RewriteRuleTokenStream stream_58=new RewriteRuleTokenStream(adaptor,"token 58");
		RewriteRuleTokenStream stream_BLOCK_BEGIN=new RewriteRuleTokenStream(adaptor,"token BLOCK_BEGIN");
		RewriteRuleTokenStream stream_BLOCK_END=new RewriteRuleTokenStream(adaptor,"token BLOCK_END");
		RewriteRuleSubtreeStream stream_expressions=new RewriteRuleSubtreeStream(adaptor,"rule expressions");

		try {
			// Dafny.g:230:10: ( ID | LIT | quantifier | '(' ! expression ')' !| '{' ( expressions )? '}' -> ^( SETEX ( expressions )? ) | '[' ( expressions )? ']' -> ^( LISTEX ( expressions )? ) )
			int alt38=6;
			switch ( input.LA(1) ) {
			case ID:
				{
				alt38=1;
				}
				break;
			case LIT:
				{
				alt38=2;
				}
				break;
			case 53:
				{
				int LA38_3 = input.LA(2);
				if ( (LA38_3==ALL||LA38_3==EX) ) {
					alt38=3;
				}
				else if ( (LA38_3==BLOCK_BEGIN||LA38_3==ID||LA38_3==LIT||(LA38_3 >= MINUS && LA38_3 <= NOT)||LA38_3==53||LA38_3==58) ) {
					alt38=4;
				}

				else {
					if (state.backtracking>0) {state.failed=true; return retval;}
					int nvaeMark = input.mark();
					try {
						input.consume();
						NoViableAltException nvae =
							new NoViableAltException("", 38, 3, input);
						throw nvae;
					} finally {
						input.rewind(nvaeMark);
					}
				}

				}
				break;
			case BLOCK_BEGIN:
				{
				alt38=5;
				}
				break;
			case 58:
				{
				alt38=6;
				}
				break;
			default:
				if (state.backtracking>0) {state.failed=true; return retval;}
				NoViableAltException nvae =
					new NoViableAltException("", 38, 0, input);
				throw nvae;
			}
			switch (alt38) {
				case 1 :
					// Dafny.g:231:5: ID
					{
					root_0 = (DafnyTree)adaptor.nil();


					ID134=(Token)match(input,ID,FOLLOW_ID_in_atom_expr1444); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					ID134_tree = (DafnyTree)adaptor.create(ID134);
					adaptor.addChild(root_0, ID134_tree);
					}

					}
					break;
				case 2 :
					// Dafny.g:232:5: LIT
					{
					root_0 = (DafnyTree)adaptor.nil();


					LIT135=(Token)match(input,LIT,FOLLOW_LIT_in_atom_expr1450); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					LIT135_tree = (DafnyTree)adaptor.create(LIT135);
					adaptor.addChild(root_0, LIT135_tree);
					}

					}
					break;
				case 3 :
					// Dafny.g:233:5: quantifier
					{
					root_0 = (DafnyTree)adaptor.nil();


					pushFollow(FOLLOW_quantifier_in_atom_expr1456);
					quantifier136=quantifier();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, quantifier136.getTree());

					}
					break;
				case 4 :
					// Dafny.g:234:5: '(' ! expression ')' !
					{
					root_0 = (DafnyTree)adaptor.nil();


					char_literal137=(Token)match(input,53,FOLLOW_53_in_atom_expr1462); if (state.failed) return retval;
					pushFollow(FOLLOW_expression_in_atom_expr1465);
					expression138=expression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, expression138.getTree());

					char_literal139=(Token)match(input,54,FOLLOW_54_in_atom_expr1467); if (state.failed) return retval;
					}
					break;
				case 5 :
					// Dafny.g:235:5: '{' ( expressions )? '}'
					{
					char_literal140=(Token)match(input,BLOCK_BEGIN,FOLLOW_BLOCK_BEGIN_in_atom_expr1474); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_BLOCK_BEGIN.add(char_literal140);

					// Dafny.g:235:9: ( expressions )?
					int alt36=2;
					int LA36_0 = input.LA(1);
					if ( (LA36_0==BLOCK_BEGIN||LA36_0==ID||LA36_0==LIT||(LA36_0 >= MINUS && LA36_0 <= NOT)||LA36_0==53||LA36_0==58) ) {
						alt36=1;
					}
					switch (alt36) {
						case 1 :
							// Dafny.g:235:9: expressions
							{
							pushFollow(FOLLOW_expressions_in_atom_expr1476);
							expressions141=expressions();
							state._fsp--;
							if (state.failed) return retval;
							if ( state.backtracking==0 ) stream_expressions.add(expressions141.getTree());
							}
							break;

					}

					char_literal142=(Token)match(input,BLOCK_END,FOLLOW_BLOCK_END_in_atom_expr1479); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_BLOCK_END.add(char_literal142);

					// AST REWRITE
					// elements: expressions
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (DafnyTree)adaptor.nil();
					// 235:26: -> ^( SETEX ( expressions )? )
					{
						// Dafny.g:235:29: ^( SETEX ( expressions )? )
						{
						DafnyTree root_1 = (DafnyTree)adaptor.nil();
						root_1 = (DafnyTree)adaptor.becomeRoot((DafnyTree)adaptor.create(SETEX, "SETEX"), root_1);
						// Dafny.g:235:37: ( expressions )?
						if ( stream_expressions.hasNext() ) {
							adaptor.addChild(root_1, stream_expressions.nextTree());
						}
						stream_expressions.reset();

						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;
				case 6 :
					// Dafny.g:236:5: '[' ( expressions )? ']'
					{
					char_literal143=(Token)match(input,58,FOLLOW_58_in_atom_expr1494); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_58.add(char_literal143);

					// Dafny.g:236:9: ( expressions )?
					int alt37=2;
					int LA37_0 = input.LA(1);
					if ( (LA37_0==BLOCK_BEGIN||LA37_0==ID||LA37_0==LIT||(LA37_0 >= MINUS && LA37_0 <= NOT)||LA37_0==53||LA37_0==58) ) {
						alt37=1;
					}
					switch (alt37) {
						case 1 :
							// Dafny.g:236:9: expressions
							{
							pushFollow(FOLLOW_expressions_in_atom_expr1496);
							expressions144=expressions();
							state._fsp--;
							if (state.failed) return retval;
							if ( state.backtracking==0 ) stream_expressions.add(expressions144.getTree());
							}
							break;

					}

					char_literal145=(Token)match(input,59,FOLLOW_59_in_atom_expr1499); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_59.add(char_literal145);

					// AST REWRITE
					// elements: expressions
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (DafnyTree)adaptor.nil();
					// 236:26: -> ^( LISTEX ( expressions )? )
					{
						// Dafny.g:236:29: ^( LISTEX ( expressions )? )
						{
						DafnyTree root_1 = (DafnyTree)adaptor.nil();
						root_1 = (DafnyTree)adaptor.becomeRoot((DafnyTree)adaptor.create(LISTEX, "LISTEX"), root_1);
						// Dafny.g:236:38: ( expressions )?
						if ( stream_expressions.hasNext() ) {
							adaptor.addChild(root_1, stream_expressions.nextTree());
						}
						stream_expressions.reset();

						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;

			}
			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (DafnyTree)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
		}

		  catch (RecognitionException e) {
		    throw e;
		  }

		finally {
			// do for sure before leaving
		}
		return retval;
	}
	// $ANTLR end "atom_expr"


	public static class quantifier_return extends ParserRuleReturnScope {
		DafnyTree tree;
		@Override
		public DafnyTree getTree() { return tree; }
	};


	// $ANTLR start "quantifier"
	// Dafny.g:239:1: quantifier : '(' ! ( ALL ^| EX ^) ID ':' ! type '::' ! expression ')' !;
	public final DafnyParser.quantifier_return quantifier() throws RecognitionException {
		DafnyParser.quantifier_return retval = new DafnyParser.quantifier_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		Token char_literal146=null;
		Token ALL147=null;
		Token EX148=null;
		Token ID149=null;
		Token char_literal150=null;
		Token string_literal152=null;
		Token char_literal154=null;
		ParserRuleReturnScope type151 =null;
		ParserRuleReturnScope expression153 =null;

		DafnyTree char_literal146_tree=null;
		DafnyTree ALL147_tree=null;
		DafnyTree EX148_tree=null;
		DafnyTree ID149_tree=null;
		DafnyTree char_literal150_tree=null;
		DafnyTree string_literal152_tree=null;
		DafnyTree char_literal154_tree=null;

		try {
			// Dafny.g:239:11: ( '(' ! ( ALL ^| EX ^) ID ':' ! type '::' ! expression ')' !)
			// Dafny.g:240:3: '(' ! ( ALL ^| EX ^) ID ':' ! type '::' ! expression ')' !
			{
			root_0 = (DafnyTree)adaptor.nil();


			char_literal146=(Token)match(input,53,FOLLOW_53_in_quantifier1520); if (state.failed) return retval;
			// Dafny.g:240:8: ( ALL ^| EX ^)
			int alt39=2;
			int LA39_0 = input.LA(1);
			if ( (LA39_0==ALL) ) {
				alt39=1;
			}
			else if ( (LA39_0==EX) ) {
				alt39=2;
			}

			else {
				if (state.backtracking>0) {state.failed=true; return retval;}
				NoViableAltException nvae =
					new NoViableAltException("", 39, 0, input);
				throw nvae;
			}

			switch (alt39) {
				case 1 :
					// Dafny.g:240:9: ALL ^
					{
					ALL147=(Token)match(input,ALL,FOLLOW_ALL_in_quantifier1524); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					ALL147_tree = (DafnyTree)adaptor.create(ALL147);
					root_0 = (DafnyTree)adaptor.becomeRoot(ALL147_tree, root_0);
					}

					}
					break;
				case 2 :
					// Dafny.g:240:16: EX ^
					{
					EX148=(Token)match(input,EX,FOLLOW_EX_in_quantifier1529); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					EX148_tree = (DafnyTree)adaptor.create(EX148);
					root_0 = (DafnyTree)adaptor.becomeRoot(EX148_tree, root_0);
					}

					}
					break;

			}

			ID149=(Token)match(input,ID,FOLLOW_ID_in_quantifier1533); if (state.failed) return retval;
			if ( state.backtracking==0 ) {
			ID149_tree = (DafnyTree)adaptor.create(ID149);
			adaptor.addChild(root_0, ID149_tree);
			}

			char_literal150=(Token)match(input,56,FOLLOW_56_in_quantifier1535); if (state.failed) return retval;
			pushFollow(FOLLOW_type_in_quantifier1538);
			type151=type();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, type151.getTree());

			string_literal152=(Token)match(input,DOUBLECOLON,FOLLOW_DOUBLECOLON_in_quantifier1540); if (state.failed) return retval;
			pushFollow(FOLLOW_expression_in_quantifier1543);
			expression153=expression();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, expression153.getTree());

			char_literal154=(Token)match(input,54,FOLLOW_54_in_quantifier1545); if (state.failed) return retval;
			}

			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (DafnyTree)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
		}

		  catch (RecognitionException e) {
		    throw e;
		  }

		finally {
			// do for sure before leaving
		}
		return retval;
	}
	// $ANTLR end "quantifier"

	// $ANTLR start synpred1_Dafny
	public final void synpred1_Dafny_fragment() throws RecognitionException {
		// Dafny.g:173:5: ( ID ':=' 'call' )
		// Dafny.g:173:6: ID ':=' 'call'
		{
		match(input,ID,FOLLOW_ID_in_synpred1_Dafny898); if (state.failed) return;

		match(input,ASSIGN,FOLLOW_ASSIGN_in_synpred1_Dafny900); if (state.failed) return;

		match(input,CALL,FOLLOW_CALL_in_synpred1_Dafny902); if (state.failed) return;

		}

	}
	// $ANTLR end synpred1_Dafny

	// Delegated rules

	public final boolean synpred1_Dafny() {
		state.backtracking++;
		int start = input.mark();
		try {
			synpred1_Dafny_fragment(); // can never throw exception
		} catch (RecognitionException re) {
			System.err.println("impossible: "+re);
		}
		boolean success = !state.failed;
		input.rewind(start);
		state.backtracking--;
		state.failed=false;
		return success;
	}



	public static final BitSet FOLLOW_method_in_program434 = new BitSet(new long[]{0x0000002100000002L});
	public static final BitSet FOLLOW_METHOD_in_method453 = new BitSet(new long[]{0x0000000001000000L});
	public static final BitSet FOLLOW_LEMMA_in_method457 = new BitSet(new long[]{0x0000000001000000L});
	public static final BitSet FOLLOW_ID_in_method462 = new BitSet(new long[]{0x0020000000000000L});
	public static final BitSet FOLLOW_53_in_method464 = new BitSet(new long[]{0x0040000001000000L});
	public static final BitSet FOLLOW_vars_in_method466 = new BitSet(new long[]{0x0040000000000000L});
	public static final BitSet FOLLOW_54_in_method469 = new BitSet(new long[]{0x0000140000089000L});
	public static final BitSet FOLLOW_returns__in_method475 = new BitSet(new long[]{0x0000040000089000L});
	public static final BitSet FOLLOW_requires_in_method484 = new BitSet(new long[]{0x0000040000089000L});
	public static final BitSet FOLLOW_ensures_in_method493 = new BitSet(new long[]{0x0000000000089000L});
	public static final BitSet FOLLOW_decreases_in_method502 = new BitSet(new long[]{0x0000000000001000L});
	public static final BitSet FOLLOW_BLOCK_BEGIN_in_method509 = new BitSet(new long[]{0x000C000043002200L});
	public static final BitSet FOLLOW_decl_in_method513 = new BitSet(new long[]{0x000C000043002200L});
	public static final BitSet FOLLOW_statements_in_method518 = new BitSet(new long[]{0x0000000000002000L});
	public static final BitSet FOLLOW_BLOCK_END_in_method521 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_VAR_in_decl586 = new BitSet(new long[]{0x0000000001000000L});
	public static final BitSet FOLLOW_var_in_decl589 = new BitSet(new long[]{0x0200000000000000L});
	public static final BitSet FOLLOW_57_in_decl591 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_var_in_vars604 = new BitSet(new long[]{0x0080000000000002L});
	public static final BitSet FOLLOW_55_in_vars610 = new BitSet(new long[]{0x0000000001000000L});
	public static final BitSet FOLLOW_var_in_vars613 = new BitSet(new long[]{0x0080000000000002L});
	public static final BitSet FOLLOW_ID_in_var628 = new BitSet(new long[]{0x0100000000000000L});
	public static final BitSet FOLLOW_56_in_var630 = new BitSet(new long[]{0x0000200008000080L});
	public static final BitSet FOLLOW_type_in_var632 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_INT_in_type656 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_SET_in_type660 = new BitSet(new long[]{0x0000001000000000L});
	public static final BitSet FOLLOW_LT_in_type663 = new BitSet(new long[]{0x0000000008000000L});
	public static final BitSet FOLLOW_INT_in_type666 = new BitSet(new long[]{0x0000000000800000L});
	public static final BitSet FOLLOW_GT_in_type668 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_ARRAY_in_type675 = new BitSet(new long[]{0x0000001000000000L});
	public static final BitSet FOLLOW_LT_in_type678 = new BitSet(new long[]{0x0000000008000000L});
	public static final BitSet FOLLOW_INT_in_type681 = new BitSet(new long[]{0x0000000000800000L});
	public static final BitSet FOLLOW_GT_in_type683 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_RETURNS_in_returns_696 = new BitSet(new long[]{0x0020000000000000L});
	public static final BitSet FOLLOW_53_in_returns_699 = new BitSet(new long[]{0x0000000001000000L});
	public static final BitSet FOLLOW_vars_in_returns_702 = new BitSet(new long[]{0x0040000000000000L});
	public static final BitSet FOLLOW_54_in_returns_704 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_REQUIRES_in_requires717 = new BitSet(new long[]{0x042000C841001000L});
	public static final BitSet FOLLOW_LABEL_in_requires721 = new BitSet(new long[]{0x0000000001000000L});
	public static final BitSet FOLLOW_ID_in_requires724 = new BitSet(new long[]{0x0100000000000000L});
	public static final BitSet FOLLOW_56_in_requires726 = new BitSet(new long[]{0x042000C801001000L});
	public static final BitSet FOLLOW_expression_in_requires731 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_ENSURES_in_ensures743 = new BitSet(new long[]{0x042000C841001000L});
	public static final BitSet FOLLOW_LABEL_in_ensures747 = new BitSet(new long[]{0x0000000001000000L});
	public static final BitSet FOLLOW_ID_in_ensures750 = new BitSet(new long[]{0x0100000000000000L});
	public static final BitSet FOLLOW_56_in_ensures752 = new BitSet(new long[]{0x042000C801001000L});
	public static final BitSet FOLLOW_expression_in_ensures757 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_DECREASES_in_decreases769 = new BitSet(new long[]{0x042000C801001000L});
	public static final BitSet FOLLOW_expression_in_decreases772 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_INVARIANT_in_invariant784 = new BitSet(new long[]{0x042000C841001000L});
	public static final BitSet FOLLOW_LABEL_in_invariant788 = new BitSet(new long[]{0x0000000001000000L});
	public static final BitSet FOLLOW_ID_in_invariant791 = new BitSet(new long[]{0x0100000000000000L});
	public static final BitSet FOLLOW_56_in_invariant793 = new BitSet(new long[]{0x042000C801001000L});
	public static final BitSet FOLLOW_expression_in_invariant798 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_BLOCK_BEGIN_in_block810 = new BitSet(new long[]{0x0008000043002200L});
	public static final BitSet FOLLOW_statements_in_block812 = new BitSet(new long[]{0x0000000000002000L});
	public static final BitSet FOLLOW_BLOCK_END_in_block815 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_block_in_relaxedBlock838 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_statement_in_relaxedBlock844 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_statement_in_statements866 = new BitSet(new long[]{0x0008000043000202L});
	public static final BitSet FOLLOW_ID_in_statement883 = new BitSet(new long[]{0x0000000000000400L});
	public static final BitSet FOLLOW_ASSIGN_in_statement885 = new BitSet(new long[]{0x042000C801001000L});
	public static final BitSet FOLLOW_expression_in_statement888 = new BitSet(new long[]{0x0200000000000000L});
	public static final BitSet FOLLOW_57_in_statement890 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_ID_in_statement909 = new BitSet(new long[]{0x0000000000000400L});
	public static final BitSet FOLLOW_ASSIGN_in_statement911 = new BitSet(new long[]{0x0000000000004000L});
	public static final BitSet FOLLOW_CALL_in_statement913 = new BitSet(new long[]{0x0000000001000000L});
	public static final BitSet FOLLOW_ID_in_statement917 = new BitSet(new long[]{0x0020000000000000L});
	public static final BitSet FOLLOW_53_in_statement919 = new BitSet(new long[]{0x046000C801001000L});
	public static final BitSet FOLLOW_expressions_in_statement921 = new BitSet(new long[]{0x0040000000000000L});
	public static final BitSet FOLLOW_54_in_statement924 = new BitSet(new long[]{0x0200000000000000L});
	public static final BitSet FOLLOW_57_in_statement926 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_ids_in_statement963 = new BitSet(new long[]{0x0000000000000400L});
	public static final BitSet FOLLOW_ASSIGN_in_statement965 = new BitSet(new long[]{0x0000000000004000L});
	public static final BitSet FOLLOW_CALL_in_statement967 = new BitSet(new long[]{0x0000000001000000L});
	public static final BitSet FOLLOW_ID_in_statement969 = new BitSet(new long[]{0x0020000000000000L});
	public static final BitSet FOLLOW_53_in_statement971 = new BitSet(new long[]{0x046000C801001000L});
	public static final BitSet FOLLOW_expressions_in_statement973 = new BitSet(new long[]{0x0040000000000000L});
	public static final BitSet FOLLOW_54_in_statement976 = new BitSet(new long[]{0x0200000000000000L});
	public static final BitSet FOLLOW_57_in_statement978 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_LABEL_in_statement1014 = new BitSet(new long[]{0x0000000001000000L});
	public static final BitSet FOLLOW_ID_in_statement1016 = new BitSet(new long[]{0x0100000000000000L});
	public static final BitSet FOLLOW_56_in_statement1018 = new BitSet(new long[]{0x0008000000000000L});
	public static final BitSet FOLLOW_WHILE_in_statement1030 = new BitSet(new long[]{0x042000C801001000L});
	public static final BitSet FOLLOW_expression_in_statement1032 = new BitSet(new long[]{0x0000000020000000L});
	public static final BitSet FOLLOW_invariant_in_statement1034 = new BitSet(new long[]{0x0000000020008000L});
	public static final BitSet FOLLOW_decreases_in_statement1037 = new BitSet(new long[]{0x0008000043001200L});
	public static final BitSet FOLLOW_relaxedBlock_in_statement1039 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_IF_in_statement1071 = new BitSet(new long[]{0x042000C801001000L});
	public static final BitSet FOLLOW_expression_in_statement1074 = new BitSet(new long[]{0x0008000043001200L});
	public static final BitSet FOLLOW_relaxedBlock_in_statement1076 = new BitSet(new long[]{0x0000000000040002L});
	public static final BitSet FOLLOW_ELSE_in_statement1097 = new BitSet(new long[]{0x0008000043001200L});
	public static final BitSet FOLLOW_relaxedBlock_in_statement1100 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_ASSERT_in_statement1109 = new BitSet(new long[]{0x042000C841001000L});
	public static final BitSet FOLLOW_LABEL_in_statement1114 = new BitSet(new long[]{0x0000000001000000L});
	public static final BitSet FOLLOW_ID_in_statement1117 = new BitSet(new long[]{0x0100000000000000L});
	public static final BitSet FOLLOW_56_in_statement1119 = new BitSet(new long[]{0x042000C801001000L});
	public static final BitSet FOLLOW_expression_in_statement1125 = new BitSet(new long[]{0x0200000000000000L});
	public static final BitSet FOLLOW_57_in_statement1127 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_ID_in_ids1140 = new BitSet(new long[]{0x0080000000000000L});
	public static final BitSet FOLLOW_55_in_ids1143 = new BitSet(new long[]{0x0000000001000000L});
	public static final BitSet FOLLOW_ID_in_ids1146 = new BitSet(new long[]{0x0080000000000002L});
	public static final BitSet FOLLOW_expression_in_expressions1160 = new BitSet(new long[]{0x0080000000000002L});
	public static final BitSet FOLLOW_55_in_expressions1164 = new BitSet(new long[]{0x042000C801001000L});
	public static final BitSet FOLLOW_expression_in_expressions1167 = new BitSet(new long[]{0x0080000000000002L});
	public static final BitSet FOLLOW_or_expr_in_expression1182 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_and_expr_in_or_expr1191 = new BitSet(new long[]{0x0000010004000002L});
	public static final BitSet FOLLOW_OR_in_or_expr1196 = new BitSet(new long[]{0x042000C801001000L});
	public static final BitSet FOLLOW_IMPLIES_in_or_expr1201 = new BitSet(new long[]{0x042000C801001000L});
	public static final BitSet FOLLOW_or_expr_in_or_expr1205 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_rel_expr_in_and_expr1220 = new BitSet(new long[]{0x0000000000000022L});
	public static final BitSet FOLLOW_AND_in_and_expr1224 = new BitSet(new long[]{0x042000C801001000L});
	public static final BitSet FOLLOW_and_expr_in_and_expr1227 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_add_expr_in_rel_expr1242 = new BitSet(new long[]{0x0000001080D00002L});
	public static final BitSet FOLLOW_LT_in_rel_expr1247 = new BitSet(new long[]{0x042000C801001000L});
	public static final BitSet FOLLOW_GT_in_rel_expr1252 = new BitSet(new long[]{0x042000C801001000L});
	public static final BitSet FOLLOW_EQ_in_rel_expr1257 = new BitSet(new long[]{0x042000C801001000L});
	public static final BitSet FOLLOW_LE_in_rel_expr1262 = new BitSet(new long[]{0x042000C801001000L});
	public static final BitSet FOLLOW_GE_in_rel_expr1267 = new BitSet(new long[]{0x042000C801001000L});
	public static final BitSet FOLLOW_add_expr_in_rel_expr1271 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_mul_expr_in_add_expr1286 = new BitSet(new long[]{0x0002024000000002L});
	public static final BitSet FOLLOW_set_in_add_expr1290 = new BitSet(new long[]{0x042000C801001000L});
	public static final BitSet FOLLOW_add_expr_in_add_expr1303 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_prefix_expr_in_mul_expr1318 = new BitSet(new long[]{0x0001000010000002L});
	public static final BitSet FOLLOW_set_in_mul_expr1322 = new BitSet(new long[]{0x042000C801001000L});
	public static final BitSet FOLLOW_mul_expr_in_mul_expr1331 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_MINUS_in_prefix_expr1348 = new BitSet(new long[]{0x042000C801001000L});
	public static final BitSet FOLLOW_prefix_expr_in_prefix_expr1351 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_NOT_in_prefix_expr1357 = new BitSet(new long[]{0x042000C801001000L});
	public static final BitSet FOLLOW_prefix_expr_in_prefix_expr1360 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_postfix_expr_in_prefix_expr1366 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_atom_expr_in_postfix_expr1378 = new BitSet(new long[]{0x0400000000010002L});
	public static final BitSet FOLLOW_58_in_postfix_expr1384 = new BitSet(new long[]{0x042000C801001000L});
	public static final BitSet FOLLOW_expression_in_postfix_expr1386 = new BitSet(new long[]{0x0800000000000000L});
	public static final BitSet FOLLOW_59_in_postfix_expr1388 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_DOT_in_postfix_expr1406 = new BitSet(new long[]{0x0000000200000000L});
	public static final BitSet FOLLOW_LENGTH_in_postfix_expr1408 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_ID_in_atom_expr1444 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_LIT_in_atom_expr1450 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_quantifier_in_atom_expr1456 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_53_in_atom_expr1462 = new BitSet(new long[]{0x042000C801001000L});
	public static final BitSet FOLLOW_expression_in_atom_expr1465 = new BitSet(new long[]{0x0040000000000000L});
	public static final BitSet FOLLOW_54_in_atom_expr1467 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_BLOCK_BEGIN_in_atom_expr1474 = new BitSet(new long[]{0x042000C801003000L});
	public static final BitSet FOLLOW_expressions_in_atom_expr1476 = new BitSet(new long[]{0x0000000000002000L});
	public static final BitSet FOLLOW_BLOCK_END_in_atom_expr1479 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_58_in_atom_expr1494 = new BitSet(new long[]{0x0C2000C801001000L});
	public static final BitSet FOLLOW_expressions_in_atom_expr1496 = new BitSet(new long[]{0x0800000000000000L});
	public static final BitSet FOLLOW_59_in_atom_expr1499 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_53_in_quantifier1520 = new BitSet(new long[]{0x0000000000200010L});
	public static final BitSet FOLLOW_ALL_in_quantifier1524 = new BitSet(new long[]{0x0000000001000000L});
	public static final BitSet FOLLOW_EX_in_quantifier1529 = new BitSet(new long[]{0x0000000001000000L});
	public static final BitSet FOLLOW_ID_in_quantifier1533 = new BitSet(new long[]{0x0100000000000000L});
	public static final BitSet FOLLOW_56_in_quantifier1535 = new BitSet(new long[]{0x0000200008000080L});
	public static final BitSet FOLLOW_type_in_quantifier1538 = new BitSet(new long[]{0x0000000000020000L});
	public static final BitSet FOLLOW_DOUBLECOLON_in_quantifier1540 = new BitSet(new long[]{0x042000C801001000L});
	public static final BitSet FOLLOW_expression_in_quantifier1543 = new BitSet(new long[]{0x0040000000000000L});
	public static final BitSet FOLLOW_54_in_quantifier1545 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_ID_in_synpred1_Dafny898 = new BitSet(new long[]{0x0000000000000400L});
	public static final BitSet FOLLOW_ASSIGN_in_synpred1_Dafny900 = new BitSet(new long[]{0x0000000000004000L});
	public static final BitSet FOLLOW_CALL_in_synpred1_Dafny902 = new BitSet(new long[]{0x0000000000000002L});
}
