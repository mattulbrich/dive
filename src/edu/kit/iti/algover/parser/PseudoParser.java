// $ANTLR 3.5.1 Pseudo.g 2015-09-11 11:23:01

  package edu.kit.iti.algover.parser;


import org.antlr.runtime.*;
import java.util.Stack;
import java.util.List;
import java.util.ArrayList;
import java.util.Map;
import java.util.HashMap;

import org.antlr.runtime.tree.*;


@SuppressWarnings("all")
public class PseudoParser extends Parser {
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


	public PseudoParser(TokenStream input) {
		this(input, new RecognizerSharedState());
	}
	public PseudoParser(TokenStream input, RecognizerSharedState state) {
		super(input, state);
	}

	protected TreeAdaptor adaptor = new CommonTreeAdaptor();

	public void setTreeAdaptor(TreeAdaptor adaptor) {
		this.adaptor = adaptor;
	}
	public TreeAdaptor getTreeAdaptor() {
		return adaptor;
	}
	@Override public String[] getTokenNames() { return PseudoParser.tokenNames; }
	@Override public String getGrammarFileName() { return "Pseudo.g"; }


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
		PseudoTree tree;
		@Override
		public PseudoTree getTree() { return tree; }
	};


	// $ANTLR start "program"
	// Pseudo.g:104:1: program : ( method )+ ;
	public final PseudoParser.program_return program() throws RecognitionException {
		PseudoParser.program_return retval = new PseudoParser.program_return();
		retval.start = input.LT(1);

		PseudoTree root_0 = null;

		ParserRuleReturnScope method1 =null;


		try {
			// Pseudo.g:104:8: ( ( method )+ )
			// Pseudo.g:105:3: ( method )+
			{
			root_0 = (PseudoTree)adaptor.nil();


			// Pseudo.g:105:3: ( method )+
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
					// Pseudo.g:105:3: method
					{
					pushFollow(FOLLOW_method_in_program446);
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
			retval.tree = (PseudoTree)adaptor.rulePostProcessing(root_0);
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
		PseudoTree tree;
		@Override
		public PseudoTree getTree() { return tree; }
	};


	// $ANTLR start "method"
	// Pseudo.g:108:1: method : ( 'method' | 'lemma' ) ID '(' ( vars )? ')' ( returns_ )? ( requires )* ( ensures )* ( decreases )? '{' ( decl )* ( statements )? '}' -> ^( METHOD ID ^( ARGS ( vars )? ) ( returns_ )? ( requires )* ( ensures )* ( decreases )? ( decl )* ^( BLOCK ( statements )? ) ) ;
	public final PseudoParser.method_return method() throws RecognitionException {
		PseudoParser.method_return retval = new PseudoParser.method_return();
		retval.start = input.LT(1);

		PseudoTree root_0 = null;

		Token string_literal2=null;
		Token string_literal3=null;
		Token ID4=null;
		Token char_literal5=null;
		Token char_literal7=null;
		Token char_literal12=null;
		Token char_literal15=null;
		ParserRuleReturnScope vars6 =null;
		ParserRuleReturnScope returns_8 =null;
		ParserRuleReturnScope requires9 =null;
		ParserRuleReturnScope ensures10 =null;
		ParserRuleReturnScope decreases11 =null;
		ParserRuleReturnScope decl13 =null;
		ParserRuleReturnScope statements14 =null;

		PseudoTree string_literal2_tree=null;
		PseudoTree string_literal3_tree=null;
		PseudoTree ID4_tree=null;
		PseudoTree char_literal5_tree=null;
		PseudoTree char_literal7_tree=null;
		PseudoTree char_literal12_tree=null;
		PseudoTree char_literal15_tree=null;
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
			// Pseudo.g:108:7: ( ( 'method' | 'lemma' ) ID '(' ( vars )? ')' ( returns_ )? ( requires )* ( ensures )* ( decreases )? '{' ( decl )* ( statements )? '}' -> ^( METHOD ID ^( ARGS ( vars )? ) ( returns_ )? ( requires )* ( ensures )* ( decreases )? ( decl )* ^( BLOCK ( statements )? ) ) )
			// Pseudo.g:109:3: ( 'method' | 'lemma' ) ID '(' ( vars )? ')' ( returns_ )? ( requires )* ( ensures )* ( decreases )? '{' ( decl )* ( statements )? '}'
			{
			// Pseudo.g:109:3: ( 'method' | 'lemma' )
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
					// Pseudo.g:109:4: 'method'
					{
					string_literal2=(Token)match(input,METHOD,FOLLOW_METHOD_in_method461); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_METHOD.add(string_literal2);

					}
					break;
				case 2 :
					// Pseudo.g:109:13: 'lemma'
					{
					string_literal3=(Token)match(input,LEMMA,FOLLOW_LEMMA_in_method463); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_LEMMA.add(string_literal3);

					}
					break;

			}

			ID4=(Token)match(input,ID,FOLLOW_ID_in_method468); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_ID.add(ID4);

			char_literal5=(Token)match(input,53,FOLLOW_53_in_method470); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_53.add(char_literal5);

			// Pseudo.g:110:10: ( vars )?
			int alt3=2;
			int LA3_0 = input.LA(1);
			if ( (LA3_0==ID) ) {
				alt3=1;
			}
			switch (alt3) {
				case 1 :
					// Pseudo.g:110:10: vars
					{
					pushFollow(FOLLOW_vars_in_method472);
					vars6=vars();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_vars.add(vars6.getTree());
					}
					break;

			}

			char_literal7=(Token)match(input,54,FOLLOW_54_in_method475); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_54.add(char_literal7);

			// Pseudo.g:111:3: ( returns_ )?
			int alt4=2;
			int LA4_0 = input.LA(1);
			if ( (LA4_0==RETURNS) ) {
				alt4=1;
			}
			switch (alt4) {
				case 1 :
					// Pseudo.g:111:5: returns_
					{
					pushFollow(FOLLOW_returns__in_method481);
					returns_8=returns_();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_returns_.add(returns_8.getTree());
					}
					break;

			}

			// Pseudo.g:112:3: ( requires )*
			loop5:
			while (true) {
				int alt5=2;
				int LA5_0 = input.LA(1);
				if ( (LA5_0==REQUIRES) ) {
					alt5=1;
				}

				switch (alt5) {
				case 1 :
					// Pseudo.g:112:5: requires
					{
					pushFollow(FOLLOW_requires_in_method490);
					requires9=requires();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_requires.add(requires9.getTree());
					}
					break;

				default :
					break loop5;
				}
			}

			// Pseudo.g:113:3: ( ensures )*
			loop6:
			while (true) {
				int alt6=2;
				int LA6_0 = input.LA(1);
				if ( (LA6_0==ENSURES) ) {
					alt6=1;
				}

				switch (alt6) {
				case 1 :
					// Pseudo.g:113:5: ensures
					{
					pushFollow(FOLLOW_ensures_in_method499);
					ensures10=ensures();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_ensures.add(ensures10.getTree());
					}
					break;

				default :
					break loop6;
				}
			}

			// Pseudo.g:114:3: ( decreases )?
			int alt7=2;
			int LA7_0 = input.LA(1);
			if ( (LA7_0==DECREASES) ) {
				alt7=1;
			}
			switch (alt7) {
				case 1 :
					// Pseudo.g:114:5: decreases
					{
					pushFollow(FOLLOW_decreases_in_method508);
					decreases11=decreases();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_decreases.add(decreases11.getTree());
					}
					break;

			}

			char_literal12=(Token)match(input,BLOCK_BEGIN,FOLLOW_BLOCK_BEGIN_in_method515); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_BLOCK_BEGIN.add(char_literal12);

			// Pseudo.g:115:7: ( decl )*
			loop8:
			while (true) {
				int alt8=2;
				int LA8_0 = input.LA(1);
				if ( (LA8_0==VAR) ) {
					alt8=1;
				}

				switch (alt8) {
				case 1 :
					// Pseudo.g:115:9: decl
					{
					pushFollow(FOLLOW_decl_in_method519);
					decl13=decl();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_decl.add(decl13.getTree());
					}
					break;

				default :
					break loop8;
				}
			}

			// Pseudo.g:115:17: ( statements )?
			int alt9=2;
			int LA9_0 = input.LA(1);
			if ( (LA9_0==ASSERT||(LA9_0 >= ID && LA9_0 <= IF)||LA9_0==LABEL||LA9_0==WHILE) ) {
				alt9=1;
			}
			switch (alt9) {
				case 1 :
					// Pseudo.g:115:17: statements
					{
					pushFollow(FOLLOW_statements_in_method524);
					statements14=statements();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_statements.add(statements14.getTree());
					}
					break;

			}

			char_literal15=(Token)match(input,BLOCK_END,FOLLOW_BLOCK_END_in_method527); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_BLOCK_END.add(char_literal15);

			// AST REWRITE
			// elements: decreases, ensures, decl, requires, statements, returns_, ID, vars
			// token labels: 
			// rule labels: retval
			// token list labels: 
			// rule list labels: 
			// wildcard labels: 
			if ( state.backtracking==0 ) {
			retval.tree = root_0;
			RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

			root_0 = (PseudoTree)adaptor.nil();
			// 116:3: -> ^( METHOD ID ^( ARGS ( vars )? ) ( returns_ )? ( requires )* ( ensures )* ( decreases )? ( decl )* ^( BLOCK ( statements )? ) )
			{
				// Pseudo.g:117:5: ^( METHOD ID ^( ARGS ( vars )? ) ( returns_ )? ( requires )* ( ensures )* ( decreases )? ( decl )* ^( BLOCK ( statements )? ) )
				{
				PseudoTree root_1 = (PseudoTree)adaptor.nil();
				root_1 = (PseudoTree)adaptor.becomeRoot((PseudoTree)adaptor.create(METHOD, "METHOD"), root_1);
				adaptor.addChild(root_1, stream_ID.nextNode());
				// Pseudo.g:117:17: ^( ARGS ( vars )? )
				{
				PseudoTree root_2 = (PseudoTree)adaptor.nil();
				root_2 = (PseudoTree)adaptor.becomeRoot((PseudoTree)adaptor.create(ARGS, "ARGS"), root_2);
				// Pseudo.g:117:24: ( vars )?
				if ( stream_vars.hasNext() ) {
					adaptor.addChild(root_2, stream_vars.nextTree());
				}
				stream_vars.reset();

				adaptor.addChild(root_1, root_2);
				}

				// Pseudo.g:117:31: ( returns_ )?
				if ( stream_returns_.hasNext() ) {
					adaptor.addChild(root_1, stream_returns_.nextTree());
				}
				stream_returns_.reset();

				// Pseudo.g:117:41: ( requires )*
				while ( stream_requires.hasNext() ) {
					adaptor.addChild(root_1, stream_requires.nextTree());
				}
				stream_requires.reset();

				// Pseudo.g:117:51: ( ensures )*
				while ( stream_ensures.hasNext() ) {
					adaptor.addChild(root_1, stream_ensures.nextTree());
				}
				stream_ensures.reset();

				// Pseudo.g:118:9: ( decreases )?
				if ( stream_decreases.hasNext() ) {
					adaptor.addChild(root_1, stream_decreases.nextTree());
				}
				stream_decreases.reset();

				// Pseudo.g:118:20: ( decl )*
				while ( stream_decl.hasNext() ) {
					adaptor.addChild(root_1, stream_decl.nextTree());
				}
				stream_decl.reset();

				// Pseudo.g:118:26: ^( BLOCK ( statements )? )
				{
				PseudoTree root_2 = (PseudoTree)adaptor.nil();
				root_2 = (PseudoTree)adaptor.becomeRoot((PseudoTree)adaptor.create(BLOCK, "BLOCK"), root_2);
				// Pseudo.g:118:34: ( statements )?
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
			retval.tree = (PseudoTree)adaptor.rulePostProcessing(root_0);
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
		PseudoTree tree;
		@Override
		public PseudoTree getTree() { return tree; }
	};


	// $ANTLR start "decl"
	// Pseudo.g:121:1: decl : VAR ! var ';' !;
	public final PseudoParser.decl_return decl() throws RecognitionException {
		PseudoParser.decl_return retval = new PseudoParser.decl_return();
		retval.start = input.LT(1);

		PseudoTree root_0 = null;

		Token VAR16=null;
		Token char_literal18=null;
		ParserRuleReturnScope var17 =null;

		PseudoTree VAR16_tree=null;
		PseudoTree char_literal18_tree=null;

		try {
			// Pseudo.g:121:5: ( VAR ! var ';' !)
			// Pseudo.g:122:3: VAR ! var ';' !
			{
			root_0 = (PseudoTree)adaptor.nil();


			VAR16=(Token)match(input,VAR,FOLLOW_VAR_in_decl591); if (state.failed) return retval;
			pushFollow(FOLLOW_var_in_decl594);
			var17=var();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, var17.getTree());

			char_literal18=(Token)match(input,57,FOLLOW_57_in_decl596); if (state.failed) return retval;
			}

			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (PseudoTree)adaptor.rulePostProcessing(root_0);
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
		PseudoTree tree;
		@Override
		public PseudoTree getTree() { return tree; }
	};


	// $ANTLR start "vars"
	// Pseudo.g:125:1: vars : var ( ',' ! var )* ;
	public final PseudoParser.vars_return vars() throws RecognitionException {
		PseudoParser.vars_return retval = new PseudoParser.vars_return();
		retval.start = input.LT(1);

		PseudoTree root_0 = null;

		Token char_literal20=null;
		ParserRuleReturnScope var19 =null;
		ParserRuleReturnScope var21 =null;

		PseudoTree char_literal20_tree=null;

		try {
			// Pseudo.g:125:5: ( var ( ',' ! var )* )
			// Pseudo.g:126:3: var ( ',' ! var )*
			{
			root_0 = (PseudoTree)adaptor.nil();


			pushFollow(FOLLOW_var_in_vars609);
			var19=var();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, var19.getTree());

			// Pseudo.g:127:3: ( ',' ! var )*
			loop10:
			while (true) {
				int alt10=2;
				int LA10_0 = input.LA(1);
				if ( (LA10_0==55) ) {
					alt10=1;
				}

				switch (alt10) {
				case 1 :
					// Pseudo.g:127:5: ',' ! var
					{
					char_literal20=(Token)match(input,55,FOLLOW_55_in_vars615); if (state.failed) return retval;
					pushFollow(FOLLOW_var_in_vars618);
					var21=var();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, var21.getTree());

					}
					break;

				default :
					break loop10;
				}
			}

			}

			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (PseudoTree)adaptor.rulePostProcessing(root_0);
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
		PseudoTree tree;
		@Override
		public PseudoTree getTree() { return tree; }
	};


	// $ANTLR start "var"
	// Pseudo.g:130:1: var : ID ':' type -> ^( VAR ID type ) ;
	public final PseudoParser.var_return var() throws RecognitionException {
		PseudoParser.var_return retval = new PseudoParser.var_return();
		retval.start = input.LT(1);

		PseudoTree root_0 = null;

		Token ID22=null;
		Token char_literal23=null;
		ParserRuleReturnScope type24 =null;

		PseudoTree ID22_tree=null;
		PseudoTree char_literal23_tree=null;
		RewriteRuleTokenStream stream_56=new RewriteRuleTokenStream(adaptor,"token 56");
		RewriteRuleTokenStream stream_ID=new RewriteRuleTokenStream(adaptor,"token ID");
		RewriteRuleSubtreeStream stream_type=new RewriteRuleSubtreeStream(adaptor,"rule type");

		try {
			// Pseudo.g:130:4: ( ID ':' type -> ^( VAR ID type ) )
			// Pseudo.g:131:3: ID ':' type
			{
			ID22=(Token)match(input,ID,FOLLOW_ID_in_var633); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_ID.add(ID22);

			char_literal23=(Token)match(input,56,FOLLOW_56_in_var635); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_56.add(char_literal23);

			pushFollow(FOLLOW_type_in_var637);
			type24=type();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) stream_type.add(type24.getTree());
			// AST REWRITE
			// elements: type, ID
			// token labels: 
			// rule labels: retval
			// token list labels: 
			// rule list labels: 
			// wildcard labels: 
			if ( state.backtracking==0 ) {
			retval.tree = root_0;
			RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

			root_0 = (PseudoTree)adaptor.nil();
			// 131:15: -> ^( VAR ID type )
			{
				// Pseudo.g:131:18: ^( VAR ID type )
				{
				PseudoTree root_1 = (PseudoTree)adaptor.nil();
				root_1 = (PseudoTree)adaptor.becomeRoot((PseudoTree)adaptor.create(VAR, "VAR"), root_1);
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
			retval.tree = (PseudoTree)adaptor.rulePostProcessing(root_0);
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
		PseudoTree tree;
		@Override
		public PseudoTree getTree() { return tree; }
	};


	// $ANTLR start "type"
	// Pseudo.g:134:1: type : ( INT | SET ^ '<' ! INT '>' !| ARRAY ^ '<' ! INT '>' !);
	public final PseudoParser.type_return type() throws RecognitionException {
		PseudoParser.type_return retval = new PseudoParser.type_return();
		retval.start = input.LT(1);

		PseudoTree root_0 = null;

		Token INT25=null;
		Token SET26=null;
		Token char_literal27=null;
		Token INT28=null;
		Token char_literal29=null;
		Token ARRAY30=null;
		Token char_literal31=null;
		Token INT32=null;
		Token char_literal33=null;

		PseudoTree INT25_tree=null;
		PseudoTree SET26_tree=null;
		PseudoTree char_literal27_tree=null;
		PseudoTree INT28_tree=null;
		PseudoTree char_literal29_tree=null;
		PseudoTree ARRAY30_tree=null;
		PseudoTree char_literal31_tree=null;
		PseudoTree INT32_tree=null;
		PseudoTree char_literal33_tree=null;

		try {
			// Pseudo.g:134:5: ( INT | SET ^ '<' ! INT '>' !| ARRAY ^ '<' ! INT '>' !)
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
					// Pseudo.g:135:5: INT
					{
					root_0 = (PseudoTree)adaptor.nil();


					INT25=(Token)match(input,INT,FOLLOW_INT_in_type661); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					INT25_tree = (PseudoTree)adaptor.create(INT25);
					adaptor.addChild(root_0, INT25_tree);
					}

					}
					break;
				case 2 :
					// Pseudo.g:135:11: SET ^ '<' ! INT '>' !
					{
					root_0 = (PseudoTree)adaptor.nil();


					SET26=(Token)match(input,SET,FOLLOW_SET_in_type665); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					SET26_tree = (PseudoTree)adaptor.create(SET26);
					root_0 = (PseudoTree)adaptor.becomeRoot(SET26_tree, root_0);
					}

					char_literal27=(Token)match(input,LT,FOLLOW_LT_in_type668); if (state.failed) return retval;
					INT28=(Token)match(input,INT,FOLLOW_INT_in_type671); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					INT28_tree = (PseudoTree)adaptor.create(INT28);
					adaptor.addChild(root_0, INT28_tree);
					}

					char_literal29=(Token)match(input,GT,FOLLOW_GT_in_type673); if (state.failed) return retval;
					}
					break;
				case 3 :
					// Pseudo.g:136:5: ARRAY ^ '<' ! INT '>' !
					{
					root_0 = (PseudoTree)adaptor.nil();


					ARRAY30=(Token)match(input,ARRAY,FOLLOW_ARRAY_in_type680); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					ARRAY30_tree = (PseudoTree)adaptor.create(ARRAY30);
					root_0 = (PseudoTree)adaptor.becomeRoot(ARRAY30_tree, root_0);
					}

					char_literal31=(Token)match(input,LT,FOLLOW_LT_in_type683); if (state.failed) return retval;
					INT32=(Token)match(input,INT,FOLLOW_INT_in_type686); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					INT32_tree = (PseudoTree)adaptor.create(INT32);
					adaptor.addChild(root_0, INT32_tree);
					}

					char_literal33=(Token)match(input,GT,FOLLOW_GT_in_type688); if (state.failed) return retval;
					}
					break;

			}
			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (PseudoTree)adaptor.rulePostProcessing(root_0);
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
		PseudoTree tree;
		@Override
		public PseudoTree getTree() { return tree; }
	};


	// $ANTLR start "returns_"
	// Pseudo.g:139:1: returns_ : RETURNS ^ '(' ! vars ')' !;
	public final PseudoParser.returns__return returns_() throws RecognitionException {
		PseudoParser.returns__return retval = new PseudoParser.returns__return();
		retval.start = input.LT(1);

		PseudoTree root_0 = null;

		Token RETURNS34=null;
		Token char_literal35=null;
		Token char_literal37=null;
		ParserRuleReturnScope vars36 =null;

		PseudoTree RETURNS34_tree=null;
		PseudoTree char_literal35_tree=null;
		PseudoTree char_literal37_tree=null;

		try {
			// Pseudo.g:139:9: ( RETURNS ^ '(' ! vars ')' !)
			// Pseudo.g:140:3: RETURNS ^ '(' ! vars ')' !
			{
			root_0 = (PseudoTree)adaptor.nil();


			RETURNS34=(Token)match(input,RETURNS,FOLLOW_RETURNS_in_returns_701); if (state.failed) return retval;
			if ( state.backtracking==0 ) {
			RETURNS34_tree = (PseudoTree)adaptor.create(RETURNS34);
			root_0 = (PseudoTree)adaptor.becomeRoot(RETURNS34_tree, root_0);
			}

			char_literal35=(Token)match(input,53,FOLLOW_53_in_returns_704); if (state.failed) return retval;
			pushFollow(FOLLOW_vars_in_returns_707);
			vars36=vars();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, vars36.getTree());

			char_literal37=(Token)match(input,54,FOLLOW_54_in_returns_709); if (state.failed) return retval;
			}

			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (PseudoTree)adaptor.rulePostProcessing(root_0);
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
		PseudoTree tree;
		@Override
		public PseudoTree getTree() { return tree; }
	};


	// $ANTLR start "requires"
	// Pseudo.g:143:1: requires : REQUIRES ^ ( 'label' ! ID ':' !)? expression ;
	public final PseudoParser.requires_return requires() throws RecognitionException {
		PseudoParser.requires_return retval = new PseudoParser.requires_return();
		retval.start = input.LT(1);

		PseudoTree root_0 = null;

		Token REQUIRES38=null;
		Token string_literal39=null;
		Token ID40=null;
		Token char_literal41=null;
		ParserRuleReturnScope expression42 =null;

		PseudoTree REQUIRES38_tree=null;
		PseudoTree string_literal39_tree=null;
		PseudoTree ID40_tree=null;
		PseudoTree char_literal41_tree=null;

		try {
			// Pseudo.g:143:9: ( REQUIRES ^ ( 'label' ! ID ':' !)? expression )
			// Pseudo.g:144:3: REQUIRES ^ ( 'label' ! ID ':' !)? expression
			{
			root_0 = (PseudoTree)adaptor.nil();


			REQUIRES38=(Token)match(input,REQUIRES,FOLLOW_REQUIRES_in_requires722); if (state.failed) return retval;
			if ( state.backtracking==0 ) {
			REQUIRES38_tree = (PseudoTree)adaptor.create(REQUIRES38);
			root_0 = (PseudoTree)adaptor.becomeRoot(REQUIRES38_tree, root_0);
			}

			// Pseudo.g:144:13: ( 'label' ! ID ':' !)?
			int alt12=2;
			int LA12_0 = input.LA(1);
			if ( (LA12_0==LABEL) ) {
				alt12=1;
			}
			switch (alt12) {
				case 1 :
					// Pseudo.g:144:14: 'label' ! ID ':' !
					{
					string_literal39=(Token)match(input,LABEL,FOLLOW_LABEL_in_requires726); if (state.failed) return retval;
					ID40=(Token)match(input,ID,FOLLOW_ID_in_requires729); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					ID40_tree = (PseudoTree)adaptor.create(ID40);
					adaptor.addChild(root_0, ID40_tree);
					}

					char_literal41=(Token)match(input,56,FOLLOW_56_in_requires731); if (state.failed) return retval;
					}
					break;

			}

			pushFollow(FOLLOW_expression_in_requires736);
			expression42=expression();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, expression42.getTree());

			}

			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (PseudoTree)adaptor.rulePostProcessing(root_0);
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
		PseudoTree tree;
		@Override
		public PseudoTree getTree() { return tree; }
	};


	// $ANTLR start "ensures"
	// Pseudo.g:147:1: ensures : ENSURES ^ ( 'label' ! ID ':' !)? expression ;
	public final PseudoParser.ensures_return ensures() throws RecognitionException {
		PseudoParser.ensures_return retval = new PseudoParser.ensures_return();
		retval.start = input.LT(1);

		PseudoTree root_0 = null;

		Token ENSURES43=null;
		Token string_literal44=null;
		Token ID45=null;
		Token char_literal46=null;
		ParserRuleReturnScope expression47 =null;

		PseudoTree ENSURES43_tree=null;
		PseudoTree string_literal44_tree=null;
		PseudoTree ID45_tree=null;
		PseudoTree char_literal46_tree=null;

		try {
			// Pseudo.g:147:8: ( ENSURES ^ ( 'label' ! ID ':' !)? expression )
			// Pseudo.g:148:3: ENSURES ^ ( 'label' ! ID ':' !)? expression
			{
			root_0 = (PseudoTree)adaptor.nil();


			ENSURES43=(Token)match(input,ENSURES,FOLLOW_ENSURES_in_ensures748); if (state.failed) return retval;
			if ( state.backtracking==0 ) {
			ENSURES43_tree = (PseudoTree)adaptor.create(ENSURES43);
			root_0 = (PseudoTree)adaptor.becomeRoot(ENSURES43_tree, root_0);
			}

			// Pseudo.g:148:12: ( 'label' ! ID ':' !)?
			int alt13=2;
			int LA13_0 = input.LA(1);
			if ( (LA13_0==LABEL) ) {
				alt13=1;
			}
			switch (alt13) {
				case 1 :
					// Pseudo.g:148:13: 'label' ! ID ':' !
					{
					string_literal44=(Token)match(input,LABEL,FOLLOW_LABEL_in_ensures752); if (state.failed) return retval;
					ID45=(Token)match(input,ID,FOLLOW_ID_in_ensures755); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					ID45_tree = (PseudoTree)adaptor.create(ID45);
					adaptor.addChild(root_0, ID45_tree);
					}

					char_literal46=(Token)match(input,56,FOLLOW_56_in_ensures757); if (state.failed) return retval;
					}
					break;

			}

			pushFollow(FOLLOW_expression_in_ensures762);
			expression47=expression();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, expression47.getTree());

			}

			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (PseudoTree)adaptor.rulePostProcessing(root_0);
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
		PseudoTree tree;
		@Override
		public PseudoTree getTree() { return tree; }
	};


	// $ANTLR start "decreases"
	// Pseudo.g:151:1: decreases : DECREASES ^ expression ;
	public final PseudoParser.decreases_return decreases() throws RecognitionException {
		PseudoParser.decreases_return retval = new PseudoParser.decreases_return();
		retval.start = input.LT(1);

		PseudoTree root_0 = null;

		Token DECREASES48=null;
		ParserRuleReturnScope expression49 =null;

		PseudoTree DECREASES48_tree=null;

		try {
			// Pseudo.g:151:10: ( DECREASES ^ expression )
			// Pseudo.g:152:3: DECREASES ^ expression
			{
			root_0 = (PseudoTree)adaptor.nil();


			DECREASES48=(Token)match(input,DECREASES,FOLLOW_DECREASES_in_decreases774); if (state.failed) return retval;
			if ( state.backtracking==0 ) {
			DECREASES48_tree = (PseudoTree)adaptor.create(DECREASES48);
			root_0 = (PseudoTree)adaptor.becomeRoot(DECREASES48_tree, root_0);
			}

			pushFollow(FOLLOW_expression_in_decreases777);
			expression49=expression();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, expression49.getTree());

			}

			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (PseudoTree)adaptor.rulePostProcessing(root_0);
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
		PseudoTree tree;
		@Override
		public PseudoTree getTree() { return tree; }
	};


	// $ANTLR start "invariant"
	// Pseudo.g:155:1: invariant : INVARIANT ^ ( 'label' ! ID ':' !)? expression ;
	public final PseudoParser.invariant_return invariant() throws RecognitionException {
		PseudoParser.invariant_return retval = new PseudoParser.invariant_return();
		retval.start = input.LT(1);

		PseudoTree root_0 = null;

		Token INVARIANT50=null;
		Token string_literal51=null;
		Token ID52=null;
		Token char_literal53=null;
		ParserRuleReturnScope expression54 =null;

		PseudoTree INVARIANT50_tree=null;
		PseudoTree string_literal51_tree=null;
		PseudoTree ID52_tree=null;
		PseudoTree char_literal53_tree=null;

		try {
			// Pseudo.g:155:10: ( INVARIANT ^ ( 'label' ! ID ':' !)? expression )
			// Pseudo.g:156:3: INVARIANT ^ ( 'label' ! ID ':' !)? expression
			{
			root_0 = (PseudoTree)adaptor.nil();


			INVARIANT50=(Token)match(input,INVARIANT,FOLLOW_INVARIANT_in_invariant789); if (state.failed) return retval;
			if ( state.backtracking==0 ) {
			INVARIANT50_tree = (PseudoTree)adaptor.create(INVARIANT50);
			root_0 = (PseudoTree)adaptor.becomeRoot(INVARIANT50_tree, root_0);
			}

			// Pseudo.g:156:14: ( 'label' ! ID ':' !)?
			int alt14=2;
			int LA14_0 = input.LA(1);
			if ( (LA14_0==LABEL) ) {
				alt14=1;
			}
			switch (alt14) {
				case 1 :
					// Pseudo.g:156:15: 'label' ! ID ':' !
					{
					string_literal51=(Token)match(input,LABEL,FOLLOW_LABEL_in_invariant793); if (state.failed) return retval;
					ID52=(Token)match(input,ID,FOLLOW_ID_in_invariant796); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					ID52_tree = (PseudoTree)adaptor.create(ID52);
					adaptor.addChild(root_0, ID52_tree);
					}

					char_literal53=(Token)match(input,56,FOLLOW_56_in_invariant798); if (state.failed) return retval;
					}
					break;

			}

			pushFollow(FOLLOW_expression_in_invariant803);
			expression54=expression();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, expression54.getTree());

			}

			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (PseudoTree)adaptor.rulePostProcessing(root_0);
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
		PseudoTree tree;
		@Override
		public PseudoTree getTree() { return tree; }
	};


	// $ANTLR start "block"
	// Pseudo.g:159:1: block : '{' ( statements )? '}' -> ^( BLOCK ( statements )? ) ;
	public final PseudoParser.block_return block() throws RecognitionException {
		PseudoParser.block_return retval = new PseudoParser.block_return();
		retval.start = input.LT(1);

		PseudoTree root_0 = null;

		Token char_literal55=null;
		Token char_literal57=null;
		ParserRuleReturnScope statements56 =null;

		PseudoTree char_literal55_tree=null;
		PseudoTree char_literal57_tree=null;
		RewriteRuleTokenStream stream_BLOCK_BEGIN=new RewriteRuleTokenStream(adaptor,"token BLOCK_BEGIN");
		RewriteRuleTokenStream stream_BLOCK_END=new RewriteRuleTokenStream(adaptor,"token BLOCK_END");
		RewriteRuleSubtreeStream stream_statements=new RewriteRuleSubtreeStream(adaptor,"rule statements");

		try {
			// Pseudo.g:159:6: ( '{' ( statements )? '}' -> ^( BLOCK ( statements )? ) )
			// Pseudo.g:160:3: '{' ( statements )? '}'
			{
			char_literal55=(Token)match(input,BLOCK_BEGIN,FOLLOW_BLOCK_BEGIN_in_block815); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_BLOCK_BEGIN.add(char_literal55);

			// Pseudo.g:160:7: ( statements )?
			int alt15=2;
			int LA15_0 = input.LA(1);
			if ( (LA15_0==ASSERT||(LA15_0 >= ID && LA15_0 <= IF)||LA15_0==LABEL||LA15_0==WHILE) ) {
				alt15=1;
			}
			switch (alt15) {
				case 1 :
					// Pseudo.g:160:7: statements
					{
					pushFollow(FOLLOW_statements_in_block817);
					statements56=statements();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_statements.add(statements56.getTree());
					}
					break;

			}

			char_literal57=(Token)match(input,BLOCK_END,FOLLOW_BLOCK_END_in_block820); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_BLOCK_END.add(char_literal57);

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

			root_0 = (PseudoTree)adaptor.nil();
			// 160:23: -> ^( BLOCK ( statements )? )
			{
				// Pseudo.g:160:26: ^( BLOCK ( statements )? )
				{
				PseudoTree root_1 = (PseudoTree)adaptor.nil();
				root_1 = (PseudoTree)adaptor.becomeRoot((PseudoTree)adaptor.create(BLOCK, "BLOCK"), root_1);
				// Pseudo.g:160:34: ( statements )?
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
			retval.tree = (PseudoTree)adaptor.rulePostProcessing(root_0);
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
		PseudoTree tree;
		@Override
		public PseudoTree getTree() { return tree; }
	};


	// $ANTLR start "relaxedBlock"
	// Pseudo.g:163:1: relaxedBlock : ( block | statement -> ^( BLOCK statement ) );
	public final PseudoParser.relaxedBlock_return relaxedBlock() throws RecognitionException {
		PseudoParser.relaxedBlock_return retval = new PseudoParser.relaxedBlock_return();
		retval.start = input.LT(1);

		PseudoTree root_0 = null;

		ParserRuleReturnScope block58 =null;
		ParserRuleReturnScope statement59 =null;

		RewriteRuleSubtreeStream stream_statement=new RewriteRuleSubtreeStream(adaptor,"rule statement");

		try {
			// Pseudo.g:163:13: ( block | statement -> ^( BLOCK statement ) )
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
					// Pseudo.g:164:5: block
					{
					root_0 = (PseudoTree)adaptor.nil();


					pushFollow(FOLLOW_block_in_relaxedBlock843);
					block58=block();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, block58.getTree());

					}
					break;
				case 2 :
					// Pseudo.g:165:5: statement
					{
					pushFollow(FOLLOW_statement_in_relaxedBlock849);
					statement59=statement();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_statement.add(statement59.getTree());
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

					root_0 = (PseudoTree)adaptor.nil();
					// 165:15: -> ^( BLOCK statement )
					{
						// Pseudo.g:165:18: ^( BLOCK statement )
						{
						PseudoTree root_1 = (PseudoTree)adaptor.nil();
						root_1 = (PseudoTree)adaptor.becomeRoot((PseudoTree)adaptor.create(BLOCK, "BLOCK"), root_1);
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
			retval.tree = (PseudoTree)adaptor.rulePostProcessing(root_0);
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
		PseudoTree tree;
		@Override
		public PseudoTree getTree() { return tree; }
	};


	// $ANTLR start "statements"
	// Pseudo.g:168:1: statements : ( statement )+ ;
	public final PseudoParser.statements_return statements() throws RecognitionException {
		PseudoParser.statements_return retval = new PseudoParser.statements_return();
		retval.start = input.LT(1);

		PseudoTree root_0 = null;

		ParserRuleReturnScope statement60 =null;


		try {
			// Pseudo.g:168:11: ( ( statement )+ )
			// Pseudo.g:169:3: ( statement )+
			{
			root_0 = (PseudoTree)adaptor.nil();


			// Pseudo.g:169:3: ( statement )+
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
					// Pseudo.g:169:5: statement
					{
					pushFollow(FOLLOW_statement_in_statements871);
					statement60=statement();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, statement60.getTree());

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
			retval.tree = (PseudoTree)adaptor.rulePostProcessing(root_0);
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
		PseudoTree tree;
		@Override
		public PseudoTree getTree() { return tree; }
	};


	// $ANTLR start "statement"
	// Pseudo.g:172:1: statement : ( ID ':=' ^ expression ';' !| ( ID ':=' 'call' )=>r= ID ':=' 'call' f= ID '(' ( expressions )? ')' ';' -> ^( 'call' $f ^( RESULTS $r) ^( ARGS ( expressions )? ) ) | ids ':=' 'call' ID '(' ( expressions )? ')' ';' -> ^( 'call' ID ^( RESULTS ids ) ^( ARGS ( expressions )? ) ) | ( 'label' ID ':' )? 'while' expression ( invariant )+ decreases relaxedBlock -> ^( 'while' ( ID )? expression ( invariant )+ decreases relaxedBlock ) | 'if' ^ expression relaxedBlock ( options {greedy=true; } : 'else' ! relaxedBlock )? | 'assert' ^ ( 'label' ! ID ':' !)? expression ';' !);
	public final PseudoParser.statement_return statement() throws RecognitionException {
		PseudoParser.statement_return retval = new PseudoParser.statement_return();
		retval.start = input.LT(1);

		PseudoTree root_0 = null;

		Token r=null;
		Token f=null;
		Token ID61=null;
		Token string_literal62=null;
		Token char_literal64=null;
		Token string_literal65=null;
		Token string_literal66=null;
		Token char_literal67=null;
		Token char_literal69=null;
		Token char_literal70=null;
		Token string_literal72=null;
		Token string_literal73=null;
		Token ID74=null;
		Token char_literal75=null;
		Token char_literal77=null;
		Token char_literal78=null;
		Token string_literal79=null;
		Token ID80=null;
		Token char_literal81=null;
		Token string_literal82=null;
		Token string_literal87=null;
		Token string_literal90=null;
		Token string_literal92=null;
		Token string_literal93=null;
		Token ID94=null;
		Token char_literal95=null;
		Token char_literal97=null;
		ParserRuleReturnScope expression63 =null;
		ParserRuleReturnScope expressions68 =null;
		ParserRuleReturnScope ids71 =null;
		ParserRuleReturnScope expressions76 =null;
		ParserRuleReturnScope expression83 =null;
		ParserRuleReturnScope invariant84 =null;
		ParserRuleReturnScope decreases85 =null;
		ParserRuleReturnScope relaxedBlock86 =null;
		ParserRuleReturnScope expression88 =null;
		ParserRuleReturnScope relaxedBlock89 =null;
		ParserRuleReturnScope relaxedBlock91 =null;
		ParserRuleReturnScope expression96 =null;

		PseudoTree r_tree=null;
		PseudoTree f_tree=null;
		PseudoTree ID61_tree=null;
		PseudoTree string_literal62_tree=null;
		PseudoTree char_literal64_tree=null;
		PseudoTree string_literal65_tree=null;
		PseudoTree string_literal66_tree=null;
		PseudoTree char_literal67_tree=null;
		PseudoTree char_literal69_tree=null;
		PseudoTree char_literal70_tree=null;
		PseudoTree string_literal72_tree=null;
		PseudoTree string_literal73_tree=null;
		PseudoTree ID74_tree=null;
		PseudoTree char_literal75_tree=null;
		PseudoTree char_literal77_tree=null;
		PseudoTree char_literal78_tree=null;
		PseudoTree string_literal79_tree=null;
		PseudoTree ID80_tree=null;
		PseudoTree char_literal81_tree=null;
		PseudoTree string_literal82_tree=null;
		PseudoTree string_literal87_tree=null;
		PseudoTree string_literal90_tree=null;
		PseudoTree string_literal92_tree=null;
		PseudoTree string_literal93_tree=null;
		PseudoTree ID94_tree=null;
		PseudoTree char_literal95_tree=null;
		PseudoTree char_literal97_tree=null;
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
			// Pseudo.g:172:10: ( ID ':=' ^ expression ';' !| ( ID ':=' 'call' )=>r= ID ':=' 'call' f= ID '(' ( expressions )? ')' ';' -> ^( 'call' $f ^( RESULTS $r) ^( ARGS ( expressions )? ) ) | ids ':=' 'call' ID '(' ( expressions )? ')' ';' -> ^( 'call' ID ^( RESULTS ids ) ^( ARGS ( expressions )? ) ) | ( 'label' ID ':' )? 'while' expression ( invariant )+ decreases relaxedBlock -> ^( 'while' ( ID )? expression ( invariant )+ decreases relaxedBlock ) | 'if' ^ expression relaxedBlock ( options {greedy=true; } : 'else' ! relaxedBlock )? | 'assert' ^ ( 'label' ! ID ':' !)? expression ';' !)
			int alt24=6;
			switch ( input.LA(1) ) {
			case ID:
				{
				int LA24_1 = input.LA(2);
				if ( (LA24_1==ASSIGN) ) {
					int LA24_5 = input.LA(3);
					if ( (LA24_5==CALL) && (synpred1_Pseudo())) {
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
					// Pseudo.g:173:5: ID ':=' ^ expression ';' !
					{
					root_0 = (PseudoTree)adaptor.nil();


					ID61=(Token)match(input,ID,FOLLOW_ID_in_statement888); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					ID61_tree = (PseudoTree)adaptor.create(ID61);
					adaptor.addChild(root_0, ID61_tree);
					}

					string_literal62=(Token)match(input,ASSIGN,FOLLOW_ASSIGN_in_statement890); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					string_literal62_tree = (PseudoTree)adaptor.create(string_literal62);
					root_0 = (PseudoTree)adaptor.becomeRoot(string_literal62_tree, root_0);
					}

					pushFollow(FOLLOW_expression_in_statement893);
					expression63=expression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, expression63.getTree());

					char_literal64=(Token)match(input,57,FOLLOW_57_in_statement895); if (state.failed) return retval;
					}
					break;
				case 2 :
					// Pseudo.g:174:5: ( ID ':=' 'call' )=>r= ID ':=' 'call' f= ID '(' ( expressions )? ')' ';'
					{
					r=(Token)match(input,ID,FOLLOW_ID_in_statement914); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_ID.add(r);

					string_literal65=(Token)match(input,ASSIGN,FOLLOW_ASSIGN_in_statement916); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_ASSIGN.add(string_literal65);

					string_literal66=(Token)match(input,CALL,FOLLOW_CALL_in_statement918); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_CALL.add(string_literal66);

					f=(Token)match(input,ID,FOLLOW_ID_in_statement922); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_ID.add(f);

					char_literal67=(Token)match(input,53,FOLLOW_53_in_statement924); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_53.add(char_literal67);

					// Pseudo.g:174:51: ( expressions )?
					int alt18=2;
					int LA18_0 = input.LA(1);
					if ( (LA18_0==BLOCK_BEGIN||LA18_0==ID||LA18_0==LIT||(LA18_0 >= MINUS && LA18_0 <= NOT)||LA18_0==53||LA18_0==58) ) {
						alt18=1;
					}
					switch (alt18) {
						case 1 :
							// Pseudo.g:174:51: expressions
							{
							pushFollow(FOLLOW_expressions_in_statement926);
							expressions68=expressions();
							state._fsp--;
							if (state.failed) return retval;
							if ( state.backtracking==0 ) stream_expressions.add(expressions68.getTree());
							}
							break;

					}

					char_literal69=(Token)match(input,54,FOLLOW_54_in_statement929); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_54.add(char_literal69);

					char_literal70=(Token)match(input,57,FOLLOW_57_in_statement931); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_57.add(char_literal70);

					// AST REWRITE
					// elements: CALL, r, f, expressions
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

					root_0 = (PseudoTree)adaptor.nil();
					// 175:9: -> ^( 'call' $f ^( RESULTS $r) ^( ARGS ( expressions )? ) )
					{
						// Pseudo.g:175:12: ^( 'call' $f ^( RESULTS $r) ^( ARGS ( expressions )? ) )
						{
						PseudoTree root_1 = (PseudoTree)adaptor.nil();
						root_1 = (PseudoTree)adaptor.becomeRoot(stream_CALL.nextNode(), root_1);
						adaptor.addChild(root_1, stream_f.nextNode());
						// Pseudo.g:175:24: ^( RESULTS $r)
						{
						PseudoTree root_2 = (PseudoTree)adaptor.nil();
						root_2 = (PseudoTree)adaptor.becomeRoot((PseudoTree)adaptor.create(RESULTS, "RESULTS"), root_2);
						adaptor.addChild(root_2, stream_r.nextNode());
						adaptor.addChild(root_1, root_2);
						}

						// Pseudo.g:175:38: ^( ARGS ( expressions )? )
						{
						PseudoTree root_2 = (PseudoTree)adaptor.nil();
						root_2 = (PseudoTree)adaptor.becomeRoot((PseudoTree)adaptor.create(ARGS, "ARGS"), root_2);
						// Pseudo.g:175:45: ( expressions )?
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
					// Pseudo.g:176:5: ids ':=' 'call' ID '(' ( expressions )? ')' ';'
					{
					pushFollow(FOLLOW_ids_in_statement968);
					ids71=ids();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_ids.add(ids71.getTree());
					string_literal72=(Token)match(input,ASSIGN,FOLLOW_ASSIGN_in_statement970); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_ASSIGN.add(string_literal72);

					string_literal73=(Token)match(input,CALL,FOLLOW_CALL_in_statement972); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_CALL.add(string_literal73);

					ID74=(Token)match(input,ID,FOLLOW_ID_in_statement974); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_ID.add(ID74);

					char_literal75=(Token)match(input,53,FOLLOW_53_in_statement976); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_53.add(char_literal75);

					// Pseudo.g:176:28: ( expressions )?
					int alt19=2;
					int LA19_0 = input.LA(1);
					if ( (LA19_0==BLOCK_BEGIN||LA19_0==ID||LA19_0==LIT||(LA19_0 >= MINUS && LA19_0 <= NOT)||LA19_0==53||LA19_0==58) ) {
						alt19=1;
					}
					switch (alt19) {
						case 1 :
							// Pseudo.g:176:28: expressions
							{
							pushFollow(FOLLOW_expressions_in_statement978);
							expressions76=expressions();
							state._fsp--;
							if (state.failed) return retval;
							if ( state.backtracking==0 ) stream_expressions.add(expressions76.getTree());
							}
							break;

					}

					char_literal77=(Token)match(input,54,FOLLOW_54_in_statement981); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_54.add(char_literal77);

					char_literal78=(Token)match(input,57,FOLLOW_57_in_statement983); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_57.add(char_literal78);

					// AST REWRITE
					// elements: ID, expressions, CALL, ids
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (PseudoTree)adaptor.nil();
					// 177:9: -> ^( 'call' ID ^( RESULTS ids ) ^( ARGS ( expressions )? ) )
					{
						// Pseudo.g:177:12: ^( 'call' ID ^( RESULTS ids ) ^( ARGS ( expressions )? ) )
						{
						PseudoTree root_1 = (PseudoTree)adaptor.nil();
						root_1 = (PseudoTree)adaptor.becomeRoot(stream_CALL.nextNode(), root_1);
						adaptor.addChild(root_1, stream_ID.nextNode());
						// Pseudo.g:177:24: ^( RESULTS ids )
						{
						PseudoTree root_2 = (PseudoTree)adaptor.nil();
						root_2 = (PseudoTree)adaptor.becomeRoot((PseudoTree)adaptor.create(RESULTS, "RESULTS"), root_2);
						adaptor.addChild(root_2, stream_ids.nextTree());
						adaptor.addChild(root_1, root_2);
						}

						// Pseudo.g:177:39: ^( ARGS ( expressions )? )
						{
						PseudoTree root_2 = (PseudoTree)adaptor.nil();
						root_2 = (PseudoTree)adaptor.becomeRoot((PseudoTree)adaptor.create(ARGS, "ARGS"), root_2);
						// Pseudo.g:177:46: ( expressions )?
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
					// Pseudo.g:178:5: ( 'label' ID ':' )? 'while' expression ( invariant )+ decreases relaxedBlock
					{
					// Pseudo.g:178:5: ( 'label' ID ':' )?
					int alt20=2;
					int LA20_0 = input.LA(1);
					if ( (LA20_0==LABEL) ) {
						alt20=1;
					}
					switch (alt20) {
						case 1 :
							// Pseudo.g:178:6: 'label' ID ':'
							{
							string_literal79=(Token)match(input,LABEL,FOLLOW_LABEL_in_statement1019); if (state.failed) return retval; 
							if ( state.backtracking==0 ) stream_LABEL.add(string_literal79);

							ID80=(Token)match(input,ID,FOLLOW_ID_in_statement1021); if (state.failed) return retval; 
							if ( state.backtracking==0 ) stream_ID.add(ID80);

							char_literal81=(Token)match(input,56,FOLLOW_56_in_statement1023); if (state.failed) return retval; 
							if ( state.backtracking==0 ) stream_56.add(char_literal81);

							}
							break;

					}

					string_literal82=(Token)match(input,WHILE,FOLLOW_WHILE_in_statement1035); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_WHILE.add(string_literal82);

					pushFollow(FOLLOW_expression_in_statement1037);
					expression83=expression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_expression.add(expression83.getTree());
					// Pseudo.g:179:26: ( invariant )+
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
							// Pseudo.g:179:26: invariant
							{
							pushFollow(FOLLOW_invariant_in_statement1039);
							invariant84=invariant();
							state._fsp--;
							if (state.failed) return retval;
							if ( state.backtracking==0 ) stream_invariant.add(invariant84.getTree());
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

					pushFollow(FOLLOW_decreases_in_statement1042);
					decreases85=decreases();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_decreases.add(decreases85.getTree());
					pushFollow(FOLLOW_relaxedBlock_in_statement1044);
					relaxedBlock86=relaxedBlock();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_relaxedBlock.add(relaxedBlock86.getTree());
					// AST REWRITE
					// elements: WHILE, decreases, relaxedBlock, expression, invariant, ID
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (PseudoTree)adaptor.nil();
					// 180:9: -> ^( 'while' ( ID )? expression ( invariant )+ decreases relaxedBlock )
					{
						// Pseudo.g:180:12: ^( 'while' ( ID )? expression ( invariant )+ decreases relaxedBlock )
						{
						PseudoTree root_1 = (PseudoTree)adaptor.nil();
						root_1 = (PseudoTree)adaptor.becomeRoot(stream_WHILE.nextNode(), root_1);
						// Pseudo.g:180:22: ( ID )?
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
					// Pseudo.g:181:5: 'if' ^ expression relaxedBlock ( options {greedy=true; } : 'else' ! relaxedBlock )?
					{
					root_0 = (PseudoTree)adaptor.nil();


					string_literal87=(Token)match(input,IF,FOLLOW_IF_in_statement1076); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					string_literal87_tree = (PseudoTree)adaptor.create(string_literal87);
					root_0 = (PseudoTree)adaptor.becomeRoot(string_literal87_tree, root_0);
					}

					pushFollow(FOLLOW_expression_in_statement1079);
					expression88=expression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, expression88.getTree());

					pushFollow(FOLLOW_relaxedBlock_in_statement1081);
					relaxedBlock89=relaxedBlock();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, relaxedBlock89.getTree());

					// Pseudo.g:182:7: ( options {greedy=true; } : 'else' ! relaxedBlock )?
					int alt22=2;
					int LA22_0 = input.LA(1);
					if ( (LA22_0==ELSE) ) {
						alt22=1;
					}
					switch (alt22) {
						case 1 :
							// Pseudo.g:182:36: 'else' ! relaxedBlock
							{
							string_literal90=(Token)match(input,ELSE,FOLLOW_ELSE_in_statement1102); if (state.failed) return retval;
							pushFollow(FOLLOW_relaxedBlock_in_statement1105);
							relaxedBlock91=relaxedBlock();
							state._fsp--;
							if (state.failed) return retval;
							if ( state.backtracking==0 ) adaptor.addChild(root_0, relaxedBlock91.getTree());

							}
							break;

					}

					}
					break;
				case 6 :
					// Pseudo.g:183:5: 'assert' ^ ( 'label' ! ID ':' !)? expression ';' !
					{
					root_0 = (PseudoTree)adaptor.nil();


					string_literal92=(Token)match(input,ASSERT,FOLLOW_ASSERT_in_statement1114); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					string_literal92_tree = (PseudoTree)adaptor.create(string_literal92);
					root_0 = (PseudoTree)adaptor.becomeRoot(string_literal92_tree, root_0);
					}

					// Pseudo.g:183:15: ( 'label' ! ID ':' !)?
					int alt23=2;
					int LA23_0 = input.LA(1);
					if ( (LA23_0==LABEL) ) {
						alt23=1;
					}
					switch (alt23) {
						case 1 :
							// Pseudo.g:183:17: 'label' ! ID ':' !
							{
							string_literal93=(Token)match(input,LABEL,FOLLOW_LABEL_in_statement1119); if (state.failed) return retval;
							ID94=(Token)match(input,ID,FOLLOW_ID_in_statement1122); if (state.failed) return retval;
							if ( state.backtracking==0 ) {
							ID94_tree = (PseudoTree)adaptor.create(ID94);
							adaptor.addChild(root_0, ID94_tree);
							}

							char_literal95=(Token)match(input,56,FOLLOW_56_in_statement1124); if (state.failed) return retval;
							}
							break;

					}

					pushFollow(FOLLOW_expression_in_statement1130);
					expression96=expression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, expression96.getTree());

					char_literal97=(Token)match(input,57,FOLLOW_57_in_statement1132); if (state.failed) return retval;
					}
					break;

			}
			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (PseudoTree)adaptor.rulePostProcessing(root_0);
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
		PseudoTree tree;
		@Override
		public PseudoTree getTree() { return tree; }
	};


	// $ANTLR start "ids"
	// Pseudo.g:186:1: ids : ID ( ',' ! ID )+ ;
	public final PseudoParser.ids_return ids() throws RecognitionException {
		PseudoParser.ids_return retval = new PseudoParser.ids_return();
		retval.start = input.LT(1);

		PseudoTree root_0 = null;

		Token ID98=null;
		Token char_literal99=null;
		Token ID100=null;

		PseudoTree ID98_tree=null;
		PseudoTree char_literal99_tree=null;
		PseudoTree ID100_tree=null;

		try {
			// Pseudo.g:186:4: ( ID ( ',' ! ID )+ )
			// Pseudo.g:187:3: ID ( ',' ! ID )+
			{
			root_0 = (PseudoTree)adaptor.nil();


			ID98=(Token)match(input,ID,FOLLOW_ID_in_ids1145); if (state.failed) return retval;
			if ( state.backtracking==0 ) {
			ID98_tree = (PseudoTree)adaptor.create(ID98);
			adaptor.addChild(root_0, ID98_tree);
			}

			// Pseudo.g:187:6: ( ',' ! ID )+
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
					// Pseudo.g:187:7: ',' ! ID
					{
					char_literal99=(Token)match(input,55,FOLLOW_55_in_ids1148); if (state.failed) return retval;
					ID100=(Token)match(input,ID,FOLLOW_ID_in_ids1151); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					ID100_tree = (PseudoTree)adaptor.create(ID100);
					adaptor.addChild(root_0, ID100_tree);
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
			retval.tree = (PseudoTree)adaptor.rulePostProcessing(root_0);
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
		PseudoTree tree;
		@Override
		public PseudoTree getTree() { return tree; }
	};


	// $ANTLR start "expressions"
	// Pseudo.g:190:1: expressions : expression ( ',' ! expression )* ;
	public final PseudoParser.expressions_return expressions() throws RecognitionException {
		PseudoParser.expressions_return retval = new PseudoParser.expressions_return();
		retval.start = input.LT(1);

		PseudoTree root_0 = null;

		Token char_literal102=null;
		ParserRuleReturnScope expression101 =null;
		ParserRuleReturnScope expression103 =null;

		PseudoTree char_literal102_tree=null;

		try {
			// Pseudo.g:190:12: ( expression ( ',' ! expression )* )
			// Pseudo.g:191:3: expression ( ',' ! expression )*
			{
			root_0 = (PseudoTree)adaptor.nil();


			pushFollow(FOLLOW_expression_in_expressions1165);
			expression101=expression();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, expression101.getTree());

			// Pseudo.g:191:14: ( ',' ! expression )*
			loop26:
			while (true) {
				int alt26=2;
				int LA26_0 = input.LA(1);
				if ( (LA26_0==55) ) {
					alt26=1;
				}

				switch (alt26) {
				case 1 :
					// Pseudo.g:191:16: ',' ! expression
					{
					char_literal102=(Token)match(input,55,FOLLOW_55_in_expressions1169); if (state.failed) return retval;
					pushFollow(FOLLOW_expression_in_expressions1172);
					expression103=expression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, expression103.getTree());

					}
					break;

				default :
					break loop26;
				}
			}

			}

			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (PseudoTree)adaptor.rulePostProcessing(root_0);
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
		PseudoTree tree;
		@Override
		public PseudoTree getTree() { return tree; }
	};


	// $ANTLR start "expression"
	// Pseudo.g:194:1: expression : or_expr ;
	public final PseudoParser.expression_return expression() throws RecognitionException {
		PseudoParser.expression_return retval = new PseudoParser.expression_return();
		retval.start = input.LT(1);

		PseudoTree root_0 = null;

		ParserRuleReturnScope or_expr104 =null;


		try {
			// Pseudo.g:194:11: ( or_expr )
			// Pseudo.g:195:3: or_expr
			{
			root_0 = (PseudoTree)adaptor.nil();


			pushFollow(FOLLOW_or_expr_in_expression1187);
			or_expr104=or_expr();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, or_expr104.getTree());

			}

			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (PseudoTree)adaptor.rulePostProcessing(root_0);
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
		PseudoTree tree;
		@Override
		public PseudoTree getTree() { return tree; }
	};


	// $ANTLR start "or_expr"
	// Pseudo.g:197:1: or_expr : and_expr ( ( '||' ^| '==>' ^) or_expr )? ;
	public final PseudoParser.or_expr_return or_expr() throws RecognitionException {
		PseudoParser.or_expr_return retval = new PseudoParser.or_expr_return();
		retval.start = input.LT(1);

		PseudoTree root_0 = null;

		Token string_literal106=null;
		Token string_literal107=null;
		ParserRuleReturnScope and_expr105 =null;
		ParserRuleReturnScope or_expr108 =null;

		PseudoTree string_literal106_tree=null;
		PseudoTree string_literal107_tree=null;

		try {
			// Pseudo.g:197:8: ( and_expr ( ( '||' ^| '==>' ^) or_expr )? )
			// Pseudo.g:198:3: and_expr ( ( '||' ^| '==>' ^) or_expr )?
			{
			root_0 = (PseudoTree)adaptor.nil();


			pushFollow(FOLLOW_and_expr_in_or_expr1196);
			and_expr105=and_expr();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, and_expr105.getTree());

			// Pseudo.g:198:12: ( ( '||' ^| '==>' ^) or_expr )?
			int alt28=2;
			int LA28_0 = input.LA(1);
			if ( (LA28_0==IMPLIES||LA28_0==OR) ) {
				alt28=1;
			}
			switch (alt28) {
				case 1 :
					// Pseudo.g:198:14: ( '||' ^| '==>' ^) or_expr
					{
					// Pseudo.g:198:14: ( '||' ^| '==>' ^)
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
							// Pseudo.g:198:15: '||' ^
							{
							string_literal106=(Token)match(input,OR,FOLLOW_OR_in_or_expr1201); if (state.failed) return retval;
							if ( state.backtracking==0 ) {
							string_literal106_tree = (PseudoTree)adaptor.create(string_literal106);
							root_0 = (PseudoTree)adaptor.becomeRoot(string_literal106_tree, root_0);
							}

							}
							break;
						case 2 :
							// Pseudo.g:198:23: '==>' ^
							{
							string_literal107=(Token)match(input,IMPLIES,FOLLOW_IMPLIES_in_or_expr1206); if (state.failed) return retval;
							if ( state.backtracking==0 ) {
							string_literal107_tree = (PseudoTree)adaptor.create(string_literal107);
							root_0 = (PseudoTree)adaptor.becomeRoot(string_literal107_tree, root_0);
							}

							}
							break;

					}

					pushFollow(FOLLOW_or_expr_in_or_expr1210);
					or_expr108=or_expr();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, or_expr108.getTree());

					}
					break;

			}

			}

			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (PseudoTree)adaptor.rulePostProcessing(root_0);
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
		PseudoTree tree;
		@Override
		public PseudoTree getTree() { return tree; }
	};


	// $ANTLR start "and_expr"
	// Pseudo.g:201:1: and_expr : rel_expr ( '&&' ^ and_expr )? ;
	public final PseudoParser.and_expr_return and_expr() throws RecognitionException {
		PseudoParser.and_expr_return retval = new PseudoParser.and_expr_return();
		retval.start = input.LT(1);

		PseudoTree root_0 = null;

		Token string_literal110=null;
		ParserRuleReturnScope rel_expr109 =null;
		ParserRuleReturnScope and_expr111 =null;

		PseudoTree string_literal110_tree=null;

		try {
			// Pseudo.g:201:9: ( rel_expr ( '&&' ^ and_expr )? )
			// Pseudo.g:202:3: rel_expr ( '&&' ^ and_expr )?
			{
			root_0 = (PseudoTree)adaptor.nil();


			pushFollow(FOLLOW_rel_expr_in_and_expr1225);
			rel_expr109=rel_expr();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, rel_expr109.getTree());

			// Pseudo.g:202:12: ( '&&' ^ and_expr )?
			int alt29=2;
			int LA29_0 = input.LA(1);
			if ( (LA29_0==AND) ) {
				alt29=1;
			}
			switch (alt29) {
				case 1 :
					// Pseudo.g:202:14: '&&' ^ and_expr
					{
					string_literal110=(Token)match(input,AND,FOLLOW_AND_in_and_expr1229); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					string_literal110_tree = (PseudoTree)adaptor.create(string_literal110);
					root_0 = (PseudoTree)adaptor.becomeRoot(string_literal110_tree, root_0);
					}

					pushFollow(FOLLOW_and_expr_in_and_expr1232);
					and_expr111=and_expr();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, and_expr111.getTree());

					}
					break;

			}

			}

			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (PseudoTree)adaptor.rulePostProcessing(root_0);
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
		PseudoTree tree;
		@Override
		public PseudoTree getTree() { return tree; }
	};


	// $ANTLR start "rel_expr"
	// Pseudo.g:205:1: rel_expr : add_expr ( ( '<' ^| '>' ^| '==' ^| '<=' ^| '>=' ^) add_expr )? ;
	public final PseudoParser.rel_expr_return rel_expr() throws RecognitionException {
		PseudoParser.rel_expr_return retval = new PseudoParser.rel_expr_return();
		retval.start = input.LT(1);

		PseudoTree root_0 = null;

		Token char_literal113=null;
		Token char_literal114=null;
		Token string_literal115=null;
		Token string_literal116=null;
		Token string_literal117=null;
		ParserRuleReturnScope add_expr112 =null;
		ParserRuleReturnScope add_expr118 =null;

		PseudoTree char_literal113_tree=null;
		PseudoTree char_literal114_tree=null;
		PseudoTree string_literal115_tree=null;
		PseudoTree string_literal116_tree=null;
		PseudoTree string_literal117_tree=null;

		try {
			// Pseudo.g:205:9: ( add_expr ( ( '<' ^| '>' ^| '==' ^| '<=' ^| '>=' ^) add_expr )? )
			// Pseudo.g:206:3: add_expr ( ( '<' ^| '>' ^| '==' ^| '<=' ^| '>=' ^) add_expr )?
			{
			root_0 = (PseudoTree)adaptor.nil();


			pushFollow(FOLLOW_add_expr_in_rel_expr1247);
			add_expr112=add_expr();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, add_expr112.getTree());

			// Pseudo.g:206:12: ( ( '<' ^| '>' ^| '==' ^| '<=' ^| '>=' ^) add_expr )?
			int alt31=2;
			int LA31_0 = input.LA(1);
			if ( (LA31_0==EQ||(LA31_0 >= GE && LA31_0 <= GT)||LA31_0==LE||LA31_0==LT) ) {
				alt31=1;
			}
			switch (alt31) {
				case 1 :
					// Pseudo.g:206:14: ( '<' ^| '>' ^| '==' ^| '<=' ^| '>=' ^) add_expr
					{
					// Pseudo.g:206:14: ( '<' ^| '>' ^| '==' ^| '<=' ^| '>=' ^)
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
							// Pseudo.g:206:15: '<' ^
							{
							char_literal113=(Token)match(input,LT,FOLLOW_LT_in_rel_expr1252); if (state.failed) return retval;
							if ( state.backtracking==0 ) {
							char_literal113_tree = (PseudoTree)adaptor.create(char_literal113);
							root_0 = (PseudoTree)adaptor.becomeRoot(char_literal113_tree, root_0);
							}

							}
							break;
						case 2 :
							// Pseudo.g:206:22: '>' ^
							{
							char_literal114=(Token)match(input,GT,FOLLOW_GT_in_rel_expr1257); if (state.failed) return retval;
							if ( state.backtracking==0 ) {
							char_literal114_tree = (PseudoTree)adaptor.create(char_literal114);
							root_0 = (PseudoTree)adaptor.becomeRoot(char_literal114_tree, root_0);
							}

							}
							break;
						case 3 :
							// Pseudo.g:206:29: '==' ^
							{
							string_literal115=(Token)match(input,EQ,FOLLOW_EQ_in_rel_expr1262); if (state.failed) return retval;
							if ( state.backtracking==0 ) {
							string_literal115_tree = (PseudoTree)adaptor.create(string_literal115);
							root_0 = (PseudoTree)adaptor.becomeRoot(string_literal115_tree, root_0);
							}

							}
							break;
						case 4 :
							// Pseudo.g:206:37: '<=' ^
							{
							string_literal116=(Token)match(input,LE,FOLLOW_LE_in_rel_expr1267); if (state.failed) return retval;
							if ( state.backtracking==0 ) {
							string_literal116_tree = (PseudoTree)adaptor.create(string_literal116);
							root_0 = (PseudoTree)adaptor.becomeRoot(string_literal116_tree, root_0);
							}

							}
							break;
						case 5 :
							// Pseudo.g:206:45: '>=' ^
							{
							string_literal117=(Token)match(input,GE,FOLLOW_GE_in_rel_expr1272); if (state.failed) return retval;
							if ( state.backtracking==0 ) {
							string_literal117_tree = (PseudoTree)adaptor.create(string_literal117);
							root_0 = (PseudoTree)adaptor.becomeRoot(string_literal117_tree, root_0);
							}

							}
							break;

					}

					pushFollow(FOLLOW_add_expr_in_rel_expr1276);
					add_expr118=add_expr();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, add_expr118.getTree());

					}
					break;

			}

			}

			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (PseudoTree)adaptor.rulePostProcessing(root_0);
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
		PseudoTree tree;
		@Override
		public PseudoTree getTree() { return tree; }
	};


	// $ANTLR start "add_expr"
	// Pseudo.g:209:1: add_expr : mul_expr ( ( '+' | '-' | '++' ) ^ add_expr )? ;
	public final PseudoParser.add_expr_return add_expr() throws RecognitionException {
		PseudoParser.add_expr_return retval = new PseudoParser.add_expr_return();
		retval.start = input.LT(1);

		PseudoTree root_0 = null;

		Token set120=null;
		ParserRuleReturnScope mul_expr119 =null;
		ParserRuleReturnScope add_expr121 =null;

		PseudoTree set120_tree=null;

		try {
			// Pseudo.g:209:9: ( mul_expr ( ( '+' | '-' | '++' ) ^ add_expr )? )
			// Pseudo.g:210:3: mul_expr ( ( '+' | '-' | '++' ) ^ add_expr )?
			{
			root_0 = (PseudoTree)adaptor.nil();


			pushFollow(FOLLOW_mul_expr_in_add_expr1291);
			mul_expr119=mul_expr();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, mul_expr119.getTree());

			// Pseudo.g:210:12: ( ( '+' | '-' | '++' ) ^ add_expr )?
			int alt32=2;
			int LA32_0 = input.LA(1);
			if ( (LA32_0==MINUS||LA32_0==PLUS||LA32_0==UNION) ) {
				alt32=1;
			}
			switch (alt32) {
				case 1 :
					// Pseudo.g:210:14: ( '+' | '-' | '++' ) ^ add_expr
					{
					set120=input.LT(1);
					set120=input.LT(1);
					if ( input.LA(1)==MINUS||input.LA(1)==PLUS||input.LA(1)==UNION ) {
						input.consume();
						if ( state.backtracking==0 ) root_0 = (PseudoTree)adaptor.becomeRoot((PseudoTree)adaptor.create(set120), root_0);
						state.errorRecovery=false;
						state.failed=false;
					}
					else {
						if (state.backtracking>0) {state.failed=true; return retval;}
						MismatchedSetException mse = new MismatchedSetException(null,input);
						throw mse;
					}
					pushFollow(FOLLOW_add_expr_in_add_expr1308);
					add_expr121=add_expr();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, add_expr121.getTree());

					}
					break;

			}

			}

			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (PseudoTree)adaptor.rulePostProcessing(root_0);
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
		PseudoTree tree;
		@Override
		public PseudoTree getTree() { return tree; }
	};


	// $ANTLR start "mul_expr"
	// Pseudo.g:213:1: mul_expr : prefix_expr ( ( '*' | '**' ) ^ mul_expr )? ;
	public final PseudoParser.mul_expr_return mul_expr() throws RecognitionException {
		PseudoParser.mul_expr_return retval = new PseudoParser.mul_expr_return();
		retval.start = input.LT(1);

		PseudoTree root_0 = null;

		Token set123=null;
		ParserRuleReturnScope prefix_expr122 =null;
		ParserRuleReturnScope mul_expr124 =null;

		PseudoTree set123_tree=null;

		try {
			// Pseudo.g:213:9: ( prefix_expr ( ( '*' | '**' ) ^ mul_expr )? )
			// Pseudo.g:214:3: prefix_expr ( ( '*' | '**' ) ^ mul_expr )?
			{
			root_0 = (PseudoTree)adaptor.nil();


			pushFollow(FOLLOW_prefix_expr_in_mul_expr1323);
			prefix_expr122=prefix_expr();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, prefix_expr122.getTree());

			// Pseudo.g:214:15: ( ( '*' | '**' ) ^ mul_expr )?
			int alt33=2;
			int LA33_0 = input.LA(1);
			if ( (LA33_0==INTERSECT||LA33_0==TIMES) ) {
				alt33=1;
			}
			switch (alt33) {
				case 1 :
					// Pseudo.g:214:17: ( '*' | '**' ) ^ mul_expr
					{
					set123=input.LT(1);
					set123=input.LT(1);
					if ( input.LA(1)==INTERSECT||input.LA(1)==TIMES ) {
						input.consume();
						if ( state.backtracking==0 ) root_0 = (PseudoTree)adaptor.becomeRoot((PseudoTree)adaptor.create(set123), root_0);
						state.errorRecovery=false;
						state.failed=false;
					}
					else {
						if (state.backtracking>0) {state.failed=true; return retval;}
						MismatchedSetException mse = new MismatchedSetException(null,input);
						throw mse;
					}
					pushFollow(FOLLOW_mul_expr_in_mul_expr1336);
					mul_expr124=mul_expr();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, mul_expr124.getTree());

					}
					break;

			}

			}

			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (PseudoTree)adaptor.rulePostProcessing(root_0);
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
		PseudoTree tree;
		@Override
		public PseudoTree getTree() { return tree; }
	};


	// $ANTLR start "prefix_expr"
	// Pseudo.g:217:1: prefix_expr : ( '-' ^ prefix_expr | '!' ^ prefix_expr | postfix_expr );
	public final PseudoParser.prefix_expr_return prefix_expr() throws RecognitionException {
		PseudoParser.prefix_expr_return retval = new PseudoParser.prefix_expr_return();
		retval.start = input.LT(1);

		PseudoTree root_0 = null;

		Token char_literal125=null;
		Token char_literal127=null;
		ParserRuleReturnScope prefix_expr126 =null;
		ParserRuleReturnScope prefix_expr128 =null;
		ParserRuleReturnScope postfix_expr129 =null;

		PseudoTree char_literal125_tree=null;
		PseudoTree char_literal127_tree=null;

		try {
			// Pseudo.g:217:12: ( '-' ^ prefix_expr | '!' ^ prefix_expr | postfix_expr )
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
					// Pseudo.g:218:5: '-' ^ prefix_expr
					{
					root_0 = (PseudoTree)adaptor.nil();


					char_literal125=(Token)match(input,MINUS,FOLLOW_MINUS_in_prefix_expr1353); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					char_literal125_tree = (PseudoTree)adaptor.create(char_literal125);
					root_0 = (PseudoTree)adaptor.becomeRoot(char_literal125_tree, root_0);
					}

					pushFollow(FOLLOW_prefix_expr_in_prefix_expr1356);
					prefix_expr126=prefix_expr();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, prefix_expr126.getTree());

					}
					break;
				case 2 :
					// Pseudo.g:219:5: '!' ^ prefix_expr
					{
					root_0 = (PseudoTree)adaptor.nil();


					char_literal127=(Token)match(input,NOT,FOLLOW_NOT_in_prefix_expr1362); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					char_literal127_tree = (PseudoTree)adaptor.create(char_literal127);
					root_0 = (PseudoTree)adaptor.becomeRoot(char_literal127_tree, root_0);
					}

					pushFollow(FOLLOW_prefix_expr_in_prefix_expr1365);
					prefix_expr128=prefix_expr();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, prefix_expr128.getTree());

					}
					break;
				case 3 :
					// Pseudo.g:220:5: postfix_expr
					{
					root_0 = (PseudoTree)adaptor.nil();


					pushFollow(FOLLOW_postfix_expr_in_prefix_expr1371);
					postfix_expr129=postfix_expr();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, postfix_expr129.getTree());

					}
					break;

			}
			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (PseudoTree)adaptor.rulePostProcessing(root_0);
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
		PseudoTree tree;
		@Override
		public PseudoTree getTree() { return tree; }
	};


	// $ANTLR start "postfix_expr"
	// Pseudo.g:223:1: postfix_expr : atom_expr ( '[' expression ']' -> ^( ARRAY_ACCESS atom_expr expression ) | '.' LENGTH -> ^( LENGTH atom_expr ) | -> atom_expr ) ;
	public final PseudoParser.postfix_expr_return postfix_expr() throws RecognitionException {
		PseudoParser.postfix_expr_return retval = new PseudoParser.postfix_expr_return();
		retval.start = input.LT(1);

		PseudoTree root_0 = null;

		Token char_literal131=null;
		Token char_literal133=null;
		Token char_literal134=null;
		Token LENGTH135=null;
		ParserRuleReturnScope atom_expr130 =null;
		ParserRuleReturnScope expression132 =null;

		PseudoTree char_literal131_tree=null;
		PseudoTree char_literal133_tree=null;
		PseudoTree char_literal134_tree=null;
		PseudoTree LENGTH135_tree=null;
		RewriteRuleTokenStream stream_59=new RewriteRuleTokenStream(adaptor,"token 59");
		RewriteRuleTokenStream stream_58=new RewriteRuleTokenStream(adaptor,"token 58");
		RewriteRuleTokenStream stream_DOT=new RewriteRuleTokenStream(adaptor,"token DOT");
		RewriteRuleTokenStream stream_LENGTH=new RewriteRuleTokenStream(adaptor,"token LENGTH");
		RewriteRuleSubtreeStream stream_expression=new RewriteRuleSubtreeStream(adaptor,"rule expression");
		RewriteRuleSubtreeStream stream_atom_expr=new RewriteRuleSubtreeStream(adaptor,"rule atom_expr");

		try {
			// Pseudo.g:223:13: ( atom_expr ( '[' expression ']' -> ^( ARRAY_ACCESS atom_expr expression ) | '.' LENGTH -> ^( LENGTH atom_expr ) | -> atom_expr ) )
			// Pseudo.g:224:3: atom_expr ( '[' expression ']' -> ^( ARRAY_ACCESS atom_expr expression ) | '.' LENGTH -> ^( LENGTH atom_expr ) | -> atom_expr )
			{
			pushFollow(FOLLOW_atom_expr_in_postfix_expr1383);
			atom_expr130=atom_expr();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) stream_atom_expr.add(atom_expr130.getTree());
			// Pseudo.g:225:3: ( '[' expression ']' -> ^( ARRAY_ACCESS atom_expr expression ) | '.' LENGTH -> ^( LENGTH atom_expr ) | -> atom_expr )
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
					// Pseudo.g:225:5: '[' expression ']'
					{
					char_literal131=(Token)match(input,58,FOLLOW_58_in_postfix_expr1389); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_58.add(char_literal131);

					pushFollow(FOLLOW_expression_in_postfix_expr1391);
					expression132=expression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_expression.add(expression132.getTree());
					char_literal133=(Token)match(input,59,FOLLOW_59_in_postfix_expr1393); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_59.add(char_literal133);

					// AST REWRITE
					// elements: atom_expr, expression
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (PseudoTree)adaptor.nil();
					// 225:24: -> ^( ARRAY_ACCESS atom_expr expression )
					{
						// Pseudo.g:225:27: ^( ARRAY_ACCESS atom_expr expression )
						{
						PseudoTree root_1 = (PseudoTree)adaptor.nil();
						root_1 = (PseudoTree)adaptor.becomeRoot((PseudoTree)adaptor.create(ARRAY_ACCESS, "ARRAY_ACCESS"), root_1);
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
					// Pseudo.g:226:5: '.' LENGTH
					{
					char_literal134=(Token)match(input,DOT,FOLLOW_DOT_in_postfix_expr1411); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_DOT.add(char_literal134);

					LENGTH135=(Token)match(input,LENGTH,FOLLOW_LENGTH_in_postfix_expr1413); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_LENGTH.add(LENGTH135);

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

					root_0 = (PseudoTree)adaptor.nil();
					// 226:16: -> ^( LENGTH atom_expr )
					{
						// Pseudo.g:226:19: ^( LENGTH atom_expr )
						{
						PseudoTree root_1 = (PseudoTree)adaptor.nil();
						root_1 = (PseudoTree)adaptor.becomeRoot(stream_LENGTH.nextNode(), root_1);
						adaptor.addChild(root_1, stream_atom_expr.nextTree());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;
				case 3 :
					// Pseudo.g:227:5: 
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

					root_0 = (PseudoTree)adaptor.nil();
					// 227:5: -> atom_expr
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
			retval.tree = (PseudoTree)adaptor.rulePostProcessing(root_0);
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
		PseudoTree tree;
		@Override
		public PseudoTree getTree() { return tree; }
	};


	// $ANTLR start "atom_expr"
	// Pseudo.g:231:1: atom_expr : ( ID | LIT | quantifier | '(' ! expression ')' !| '{' ( expressions )? '}' -> ^( SETEX ( expressions )? ) | '[' ( expressions )? ']' -> ^( LISTEX ( expressions )? ) );
	public final PseudoParser.atom_expr_return atom_expr() throws RecognitionException {
		PseudoParser.atom_expr_return retval = new PseudoParser.atom_expr_return();
		retval.start = input.LT(1);

		PseudoTree root_0 = null;

		Token ID136=null;
		Token LIT137=null;
		Token char_literal139=null;
		Token char_literal141=null;
		Token char_literal142=null;
		Token char_literal144=null;
		Token char_literal145=null;
		Token char_literal147=null;
		ParserRuleReturnScope quantifier138 =null;
		ParserRuleReturnScope expression140 =null;
		ParserRuleReturnScope expressions143 =null;
		ParserRuleReturnScope expressions146 =null;

		PseudoTree ID136_tree=null;
		PseudoTree LIT137_tree=null;
		PseudoTree char_literal139_tree=null;
		PseudoTree char_literal141_tree=null;
		PseudoTree char_literal142_tree=null;
		PseudoTree char_literal144_tree=null;
		PseudoTree char_literal145_tree=null;
		PseudoTree char_literal147_tree=null;
		RewriteRuleTokenStream stream_59=new RewriteRuleTokenStream(adaptor,"token 59");
		RewriteRuleTokenStream stream_58=new RewriteRuleTokenStream(adaptor,"token 58");
		RewriteRuleTokenStream stream_BLOCK_BEGIN=new RewriteRuleTokenStream(adaptor,"token BLOCK_BEGIN");
		RewriteRuleTokenStream stream_BLOCK_END=new RewriteRuleTokenStream(adaptor,"token BLOCK_END");
		RewriteRuleSubtreeStream stream_expressions=new RewriteRuleSubtreeStream(adaptor,"rule expressions");

		try {
			// Pseudo.g:231:10: ( ID | LIT | quantifier | '(' ! expression ')' !| '{' ( expressions )? '}' -> ^( SETEX ( expressions )? ) | '[' ( expressions )? ']' -> ^( LISTEX ( expressions )? ) )
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
					// Pseudo.g:232:5: ID
					{
					root_0 = (PseudoTree)adaptor.nil();


					ID136=(Token)match(input,ID,FOLLOW_ID_in_atom_expr1449); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					ID136_tree = (PseudoTree)adaptor.create(ID136);
					adaptor.addChild(root_0, ID136_tree);
					}

					}
					break;
				case 2 :
					// Pseudo.g:233:5: LIT
					{
					root_0 = (PseudoTree)adaptor.nil();


					LIT137=(Token)match(input,LIT,FOLLOW_LIT_in_atom_expr1455); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					LIT137_tree = (PseudoTree)adaptor.create(LIT137);
					adaptor.addChild(root_0, LIT137_tree);
					}

					}
					break;
				case 3 :
					// Pseudo.g:234:5: quantifier
					{
					root_0 = (PseudoTree)adaptor.nil();


					pushFollow(FOLLOW_quantifier_in_atom_expr1461);
					quantifier138=quantifier();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, quantifier138.getTree());

					}
					break;
				case 4 :
					// Pseudo.g:235:5: '(' ! expression ')' !
					{
					root_0 = (PseudoTree)adaptor.nil();


					char_literal139=(Token)match(input,53,FOLLOW_53_in_atom_expr1467); if (state.failed) return retval;
					pushFollow(FOLLOW_expression_in_atom_expr1470);
					expression140=expression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, expression140.getTree());

					char_literal141=(Token)match(input,54,FOLLOW_54_in_atom_expr1472); if (state.failed) return retval;
					}
					break;
				case 5 :
					// Pseudo.g:236:5: '{' ( expressions )? '}'
					{
					char_literal142=(Token)match(input,BLOCK_BEGIN,FOLLOW_BLOCK_BEGIN_in_atom_expr1479); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_BLOCK_BEGIN.add(char_literal142);

					// Pseudo.g:236:9: ( expressions )?
					int alt36=2;
					int LA36_0 = input.LA(1);
					if ( (LA36_0==BLOCK_BEGIN||LA36_0==ID||LA36_0==LIT||(LA36_0 >= MINUS && LA36_0 <= NOT)||LA36_0==53||LA36_0==58) ) {
						alt36=1;
					}
					switch (alt36) {
						case 1 :
							// Pseudo.g:236:9: expressions
							{
							pushFollow(FOLLOW_expressions_in_atom_expr1481);
							expressions143=expressions();
							state._fsp--;
							if (state.failed) return retval;
							if ( state.backtracking==0 ) stream_expressions.add(expressions143.getTree());
							}
							break;

					}

					char_literal144=(Token)match(input,BLOCK_END,FOLLOW_BLOCK_END_in_atom_expr1484); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_BLOCK_END.add(char_literal144);

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

					root_0 = (PseudoTree)adaptor.nil();
					// 236:26: -> ^( SETEX ( expressions )? )
					{
						// Pseudo.g:236:29: ^( SETEX ( expressions )? )
						{
						PseudoTree root_1 = (PseudoTree)adaptor.nil();
						root_1 = (PseudoTree)adaptor.becomeRoot((PseudoTree)adaptor.create(SETEX, "SETEX"), root_1);
						// Pseudo.g:236:37: ( expressions )?
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
					// Pseudo.g:237:5: '[' ( expressions )? ']'
					{
					char_literal145=(Token)match(input,58,FOLLOW_58_in_atom_expr1499); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_58.add(char_literal145);

					// Pseudo.g:237:9: ( expressions )?
					int alt37=2;
					int LA37_0 = input.LA(1);
					if ( (LA37_0==BLOCK_BEGIN||LA37_0==ID||LA37_0==LIT||(LA37_0 >= MINUS && LA37_0 <= NOT)||LA37_0==53||LA37_0==58) ) {
						alt37=1;
					}
					switch (alt37) {
						case 1 :
							// Pseudo.g:237:9: expressions
							{
							pushFollow(FOLLOW_expressions_in_atom_expr1501);
							expressions146=expressions();
							state._fsp--;
							if (state.failed) return retval;
							if ( state.backtracking==0 ) stream_expressions.add(expressions146.getTree());
							}
							break;

					}

					char_literal147=(Token)match(input,59,FOLLOW_59_in_atom_expr1504); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_59.add(char_literal147);

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

					root_0 = (PseudoTree)adaptor.nil();
					// 237:26: -> ^( LISTEX ( expressions )? )
					{
						// Pseudo.g:237:29: ^( LISTEX ( expressions )? )
						{
						PseudoTree root_1 = (PseudoTree)adaptor.nil();
						root_1 = (PseudoTree)adaptor.becomeRoot((PseudoTree)adaptor.create(LISTEX, "LISTEX"), root_1);
						// Pseudo.g:237:38: ( expressions )?
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
			retval.tree = (PseudoTree)adaptor.rulePostProcessing(root_0);
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
		PseudoTree tree;
		@Override
		public PseudoTree getTree() { return tree; }
	};


	// $ANTLR start "quantifier"
	// Pseudo.g:240:1: quantifier : '(' ! ( ALL ^| EX ^) ID ':' ! type '::' ! expression ')' !;
	public final PseudoParser.quantifier_return quantifier() throws RecognitionException {
		PseudoParser.quantifier_return retval = new PseudoParser.quantifier_return();
		retval.start = input.LT(1);

		PseudoTree root_0 = null;

		Token char_literal148=null;
		Token ALL149=null;
		Token EX150=null;
		Token ID151=null;
		Token char_literal152=null;
		Token string_literal154=null;
		Token char_literal156=null;
		ParserRuleReturnScope type153 =null;
		ParserRuleReturnScope expression155 =null;

		PseudoTree char_literal148_tree=null;
		PseudoTree ALL149_tree=null;
		PseudoTree EX150_tree=null;
		PseudoTree ID151_tree=null;
		PseudoTree char_literal152_tree=null;
		PseudoTree string_literal154_tree=null;
		PseudoTree char_literal156_tree=null;

		try {
			// Pseudo.g:240:11: ( '(' ! ( ALL ^| EX ^) ID ':' ! type '::' ! expression ')' !)
			// Pseudo.g:241:3: '(' ! ( ALL ^| EX ^) ID ':' ! type '::' ! expression ')' !
			{
			root_0 = (PseudoTree)adaptor.nil();


			char_literal148=(Token)match(input,53,FOLLOW_53_in_quantifier1525); if (state.failed) return retval;
			// Pseudo.g:241:8: ( ALL ^| EX ^)
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
					// Pseudo.g:241:9: ALL ^
					{
					ALL149=(Token)match(input,ALL,FOLLOW_ALL_in_quantifier1529); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					ALL149_tree = (PseudoTree)adaptor.create(ALL149);
					root_0 = (PseudoTree)adaptor.becomeRoot(ALL149_tree, root_0);
					}

					}
					break;
				case 2 :
					// Pseudo.g:241:16: EX ^
					{
					EX150=(Token)match(input,EX,FOLLOW_EX_in_quantifier1534); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					EX150_tree = (PseudoTree)adaptor.create(EX150);
					root_0 = (PseudoTree)adaptor.becomeRoot(EX150_tree, root_0);
					}

					}
					break;

			}

			ID151=(Token)match(input,ID,FOLLOW_ID_in_quantifier1538); if (state.failed) return retval;
			if ( state.backtracking==0 ) {
			ID151_tree = (PseudoTree)adaptor.create(ID151);
			adaptor.addChild(root_0, ID151_tree);
			}

			char_literal152=(Token)match(input,56,FOLLOW_56_in_quantifier1540); if (state.failed) return retval;
			pushFollow(FOLLOW_type_in_quantifier1543);
			type153=type();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, type153.getTree());

			string_literal154=(Token)match(input,DOUBLECOLON,FOLLOW_DOUBLECOLON_in_quantifier1545); if (state.failed) return retval;
			pushFollow(FOLLOW_expression_in_quantifier1548);
			expression155=expression();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, expression155.getTree());

			char_literal156=(Token)match(input,54,FOLLOW_54_in_quantifier1550); if (state.failed) return retval;
			}

			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (PseudoTree)adaptor.rulePostProcessing(root_0);
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

	// $ANTLR start synpred1_Pseudo
	public final void synpred1_Pseudo_fragment() throws RecognitionException {
		// Pseudo.g:174:5: ( ID ':=' 'call' )
		// Pseudo.g:174:6: ID ':=' 'call'
		{
		match(input,ID,FOLLOW_ID_in_synpred1_Pseudo903); if (state.failed) return;

		match(input,ASSIGN,FOLLOW_ASSIGN_in_synpred1_Pseudo905); if (state.failed) return;

		match(input,CALL,FOLLOW_CALL_in_synpred1_Pseudo907); if (state.failed) return;

		}

	}
	// $ANTLR end synpred1_Pseudo

	// Delegated rules

	public final boolean synpred1_Pseudo() {
		state.backtracking++;
		int start = input.mark();
		try {
			synpred1_Pseudo_fragment(); // can never throw exception
		} catch (RecognitionException re) {
			System.err.println("impossible: "+re);
		}
		boolean success = !state.failed;
		input.rewind(start);
		state.backtracking--;
		state.failed=false;
		return success;
	}



	public static final BitSet FOLLOW_method_in_program446 = new BitSet(new long[]{0x0000002100000002L});
	public static final BitSet FOLLOW_METHOD_in_method461 = new BitSet(new long[]{0x0000000001000000L});
	public static final BitSet FOLLOW_LEMMA_in_method463 = new BitSet(new long[]{0x0000000001000000L});
	public static final BitSet FOLLOW_ID_in_method468 = new BitSet(new long[]{0x0020000000000000L});
	public static final BitSet FOLLOW_53_in_method470 = new BitSet(new long[]{0x0040000001000000L});
	public static final BitSet FOLLOW_vars_in_method472 = new BitSet(new long[]{0x0040000000000000L});
	public static final BitSet FOLLOW_54_in_method475 = new BitSet(new long[]{0x0000140000089000L});
	public static final BitSet FOLLOW_returns__in_method481 = new BitSet(new long[]{0x0000040000089000L});
	public static final BitSet FOLLOW_requires_in_method490 = new BitSet(new long[]{0x0000040000089000L});
	public static final BitSet FOLLOW_ensures_in_method499 = new BitSet(new long[]{0x0000000000089000L});
	public static final BitSet FOLLOW_decreases_in_method508 = new BitSet(new long[]{0x0000000000001000L});
	public static final BitSet FOLLOW_BLOCK_BEGIN_in_method515 = new BitSet(new long[]{0x000C000043002200L});
	public static final BitSet FOLLOW_decl_in_method519 = new BitSet(new long[]{0x000C000043002200L});
	public static final BitSet FOLLOW_statements_in_method524 = new BitSet(new long[]{0x0000000000002000L});
	public static final BitSet FOLLOW_BLOCK_END_in_method527 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_VAR_in_decl591 = new BitSet(new long[]{0x0000000001000000L});
	public static final BitSet FOLLOW_var_in_decl594 = new BitSet(new long[]{0x0200000000000000L});
	public static final BitSet FOLLOW_57_in_decl596 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_var_in_vars609 = new BitSet(new long[]{0x0080000000000002L});
	public static final BitSet FOLLOW_55_in_vars615 = new BitSet(new long[]{0x0000000001000000L});
	public static final BitSet FOLLOW_var_in_vars618 = new BitSet(new long[]{0x0080000000000002L});
	public static final BitSet FOLLOW_ID_in_var633 = new BitSet(new long[]{0x0100000000000000L});
	public static final BitSet FOLLOW_56_in_var635 = new BitSet(new long[]{0x0000200008000080L});
	public static final BitSet FOLLOW_type_in_var637 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_INT_in_type661 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_SET_in_type665 = new BitSet(new long[]{0x0000001000000000L});
	public static final BitSet FOLLOW_LT_in_type668 = new BitSet(new long[]{0x0000000008000000L});
	public static final BitSet FOLLOW_INT_in_type671 = new BitSet(new long[]{0x0000000000800000L});
	public static final BitSet FOLLOW_GT_in_type673 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_ARRAY_in_type680 = new BitSet(new long[]{0x0000001000000000L});
	public static final BitSet FOLLOW_LT_in_type683 = new BitSet(new long[]{0x0000000008000000L});
	public static final BitSet FOLLOW_INT_in_type686 = new BitSet(new long[]{0x0000000000800000L});
	public static final BitSet FOLLOW_GT_in_type688 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_RETURNS_in_returns_701 = new BitSet(new long[]{0x0020000000000000L});
	public static final BitSet FOLLOW_53_in_returns_704 = new BitSet(new long[]{0x0000000001000000L});
	public static final BitSet FOLLOW_vars_in_returns_707 = new BitSet(new long[]{0x0040000000000000L});
	public static final BitSet FOLLOW_54_in_returns_709 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_REQUIRES_in_requires722 = new BitSet(new long[]{0x042000C841001000L});
	public static final BitSet FOLLOW_LABEL_in_requires726 = new BitSet(new long[]{0x0000000001000000L});
	public static final BitSet FOLLOW_ID_in_requires729 = new BitSet(new long[]{0x0100000000000000L});
	public static final BitSet FOLLOW_56_in_requires731 = new BitSet(new long[]{0x042000C801001000L});
	public static final BitSet FOLLOW_expression_in_requires736 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_ENSURES_in_ensures748 = new BitSet(new long[]{0x042000C841001000L});
	public static final BitSet FOLLOW_LABEL_in_ensures752 = new BitSet(new long[]{0x0000000001000000L});
	public static final BitSet FOLLOW_ID_in_ensures755 = new BitSet(new long[]{0x0100000000000000L});
	public static final BitSet FOLLOW_56_in_ensures757 = new BitSet(new long[]{0x042000C801001000L});
	public static final BitSet FOLLOW_expression_in_ensures762 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_DECREASES_in_decreases774 = new BitSet(new long[]{0x042000C801001000L});
	public static final BitSet FOLLOW_expression_in_decreases777 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_INVARIANT_in_invariant789 = new BitSet(new long[]{0x042000C841001000L});
	public static final BitSet FOLLOW_LABEL_in_invariant793 = new BitSet(new long[]{0x0000000001000000L});
	public static final BitSet FOLLOW_ID_in_invariant796 = new BitSet(new long[]{0x0100000000000000L});
	public static final BitSet FOLLOW_56_in_invariant798 = new BitSet(new long[]{0x042000C801001000L});
	public static final BitSet FOLLOW_expression_in_invariant803 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_BLOCK_BEGIN_in_block815 = new BitSet(new long[]{0x0008000043002200L});
	public static final BitSet FOLLOW_statements_in_block817 = new BitSet(new long[]{0x0000000000002000L});
	public static final BitSet FOLLOW_BLOCK_END_in_block820 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_block_in_relaxedBlock843 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_statement_in_relaxedBlock849 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_statement_in_statements871 = new BitSet(new long[]{0x0008000043000202L});
	public static final BitSet FOLLOW_ID_in_statement888 = new BitSet(new long[]{0x0000000000000400L});
	public static final BitSet FOLLOW_ASSIGN_in_statement890 = new BitSet(new long[]{0x042000C801001000L});
	public static final BitSet FOLLOW_expression_in_statement893 = new BitSet(new long[]{0x0200000000000000L});
	public static final BitSet FOLLOW_57_in_statement895 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_ID_in_statement914 = new BitSet(new long[]{0x0000000000000400L});
	public static final BitSet FOLLOW_ASSIGN_in_statement916 = new BitSet(new long[]{0x0000000000004000L});
	public static final BitSet FOLLOW_CALL_in_statement918 = new BitSet(new long[]{0x0000000001000000L});
	public static final BitSet FOLLOW_ID_in_statement922 = new BitSet(new long[]{0x0020000000000000L});
	public static final BitSet FOLLOW_53_in_statement924 = new BitSet(new long[]{0x046000C801001000L});
	public static final BitSet FOLLOW_expressions_in_statement926 = new BitSet(new long[]{0x0040000000000000L});
	public static final BitSet FOLLOW_54_in_statement929 = new BitSet(new long[]{0x0200000000000000L});
	public static final BitSet FOLLOW_57_in_statement931 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_ids_in_statement968 = new BitSet(new long[]{0x0000000000000400L});
	public static final BitSet FOLLOW_ASSIGN_in_statement970 = new BitSet(new long[]{0x0000000000004000L});
	public static final BitSet FOLLOW_CALL_in_statement972 = new BitSet(new long[]{0x0000000001000000L});
	public static final BitSet FOLLOW_ID_in_statement974 = new BitSet(new long[]{0x0020000000000000L});
	public static final BitSet FOLLOW_53_in_statement976 = new BitSet(new long[]{0x046000C801001000L});
	public static final BitSet FOLLOW_expressions_in_statement978 = new BitSet(new long[]{0x0040000000000000L});
	public static final BitSet FOLLOW_54_in_statement981 = new BitSet(new long[]{0x0200000000000000L});
	public static final BitSet FOLLOW_57_in_statement983 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_LABEL_in_statement1019 = new BitSet(new long[]{0x0000000001000000L});
	public static final BitSet FOLLOW_ID_in_statement1021 = new BitSet(new long[]{0x0100000000000000L});
	public static final BitSet FOLLOW_56_in_statement1023 = new BitSet(new long[]{0x0008000000000000L});
	public static final BitSet FOLLOW_WHILE_in_statement1035 = new BitSet(new long[]{0x042000C801001000L});
	public static final BitSet FOLLOW_expression_in_statement1037 = new BitSet(new long[]{0x0000000020000000L});
	public static final BitSet FOLLOW_invariant_in_statement1039 = new BitSet(new long[]{0x0000000020008000L});
	public static final BitSet FOLLOW_decreases_in_statement1042 = new BitSet(new long[]{0x0008000043001200L});
	public static final BitSet FOLLOW_relaxedBlock_in_statement1044 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_IF_in_statement1076 = new BitSet(new long[]{0x042000C801001000L});
	public static final BitSet FOLLOW_expression_in_statement1079 = new BitSet(new long[]{0x0008000043001200L});
	public static final BitSet FOLLOW_relaxedBlock_in_statement1081 = new BitSet(new long[]{0x0000000000040002L});
	public static final BitSet FOLLOW_ELSE_in_statement1102 = new BitSet(new long[]{0x0008000043001200L});
	public static final BitSet FOLLOW_relaxedBlock_in_statement1105 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_ASSERT_in_statement1114 = new BitSet(new long[]{0x042000C841001000L});
	public static final BitSet FOLLOW_LABEL_in_statement1119 = new BitSet(new long[]{0x0000000001000000L});
	public static final BitSet FOLLOW_ID_in_statement1122 = new BitSet(new long[]{0x0100000000000000L});
	public static final BitSet FOLLOW_56_in_statement1124 = new BitSet(new long[]{0x042000C801001000L});
	public static final BitSet FOLLOW_expression_in_statement1130 = new BitSet(new long[]{0x0200000000000000L});
	public static final BitSet FOLLOW_57_in_statement1132 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_ID_in_ids1145 = new BitSet(new long[]{0x0080000000000000L});
	public static final BitSet FOLLOW_55_in_ids1148 = new BitSet(new long[]{0x0000000001000000L});
	public static final BitSet FOLLOW_ID_in_ids1151 = new BitSet(new long[]{0x0080000000000002L});
	public static final BitSet FOLLOW_expression_in_expressions1165 = new BitSet(new long[]{0x0080000000000002L});
	public static final BitSet FOLLOW_55_in_expressions1169 = new BitSet(new long[]{0x042000C801001000L});
	public static final BitSet FOLLOW_expression_in_expressions1172 = new BitSet(new long[]{0x0080000000000002L});
	public static final BitSet FOLLOW_or_expr_in_expression1187 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_and_expr_in_or_expr1196 = new BitSet(new long[]{0x0000010004000002L});
	public static final BitSet FOLLOW_OR_in_or_expr1201 = new BitSet(new long[]{0x042000C801001000L});
	public static final BitSet FOLLOW_IMPLIES_in_or_expr1206 = new BitSet(new long[]{0x042000C801001000L});
	public static final BitSet FOLLOW_or_expr_in_or_expr1210 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_rel_expr_in_and_expr1225 = new BitSet(new long[]{0x0000000000000022L});
	public static final BitSet FOLLOW_AND_in_and_expr1229 = new BitSet(new long[]{0x042000C801001000L});
	public static final BitSet FOLLOW_and_expr_in_and_expr1232 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_add_expr_in_rel_expr1247 = new BitSet(new long[]{0x0000001080D00002L});
	public static final BitSet FOLLOW_LT_in_rel_expr1252 = new BitSet(new long[]{0x042000C801001000L});
	public static final BitSet FOLLOW_GT_in_rel_expr1257 = new BitSet(new long[]{0x042000C801001000L});
	public static final BitSet FOLLOW_EQ_in_rel_expr1262 = new BitSet(new long[]{0x042000C801001000L});
	public static final BitSet FOLLOW_LE_in_rel_expr1267 = new BitSet(new long[]{0x042000C801001000L});
	public static final BitSet FOLLOW_GE_in_rel_expr1272 = new BitSet(new long[]{0x042000C801001000L});
	public static final BitSet FOLLOW_add_expr_in_rel_expr1276 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_mul_expr_in_add_expr1291 = new BitSet(new long[]{0x0002024000000002L});
	public static final BitSet FOLLOW_set_in_add_expr1295 = new BitSet(new long[]{0x042000C801001000L});
	public static final BitSet FOLLOW_add_expr_in_add_expr1308 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_prefix_expr_in_mul_expr1323 = new BitSet(new long[]{0x0001000010000002L});
	public static final BitSet FOLLOW_set_in_mul_expr1327 = new BitSet(new long[]{0x042000C801001000L});
	public static final BitSet FOLLOW_mul_expr_in_mul_expr1336 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_MINUS_in_prefix_expr1353 = new BitSet(new long[]{0x042000C801001000L});
	public static final BitSet FOLLOW_prefix_expr_in_prefix_expr1356 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_NOT_in_prefix_expr1362 = new BitSet(new long[]{0x042000C801001000L});
	public static final BitSet FOLLOW_prefix_expr_in_prefix_expr1365 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_postfix_expr_in_prefix_expr1371 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_atom_expr_in_postfix_expr1383 = new BitSet(new long[]{0x0400000000010002L});
	public static final BitSet FOLLOW_58_in_postfix_expr1389 = new BitSet(new long[]{0x042000C801001000L});
	public static final BitSet FOLLOW_expression_in_postfix_expr1391 = new BitSet(new long[]{0x0800000000000000L});
	public static final BitSet FOLLOW_59_in_postfix_expr1393 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_DOT_in_postfix_expr1411 = new BitSet(new long[]{0x0000000200000000L});
	public static final BitSet FOLLOW_LENGTH_in_postfix_expr1413 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_ID_in_atom_expr1449 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_LIT_in_atom_expr1455 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_quantifier_in_atom_expr1461 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_53_in_atom_expr1467 = new BitSet(new long[]{0x042000C801001000L});
	public static final BitSet FOLLOW_expression_in_atom_expr1470 = new BitSet(new long[]{0x0040000000000000L});
	public static final BitSet FOLLOW_54_in_atom_expr1472 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_BLOCK_BEGIN_in_atom_expr1479 = new BitSet(new long[]{0x042000C801003000L});
	public static final BitSet FOLLOW_expressions_in_atom_expr1481 = new BitSet(new long[]{0x0000000000002000L});
	public static final BitSet FOLLOW_BLOCK_END_in_atom_expr1484 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_58_in_atom_expr1499 = new BitSet(new long[]{0x0C2000C801001000L});
	public static final BitSet FOLLOW_expressions_in_atom_expr1501 = new BitSet(new long[]{0x0800000000000000L});
	public static final BitSet FOLLOW_59_in_atom_expr1504 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_53_in_quantifier1525 = new BitSet(new long[]{0x0000000000200010L});
	public static final BitSet FOLLOW_ALL_in_quantifier1529 = new BitSet(new long[]{0x0000000001000000L});
	public static final BitSet FOLLOW_EX_in_quantifier1534 = new BitSet(new long[]{0x0000000001000000L});
	public static final BitSet FOLLOW_ID_in_quantifier1538 = new BitSet(new long[]{0x0100000000000000L});
	public static final BitSet FOLLOW_56_in_quantifier1540 = new BitSet(new long[]{0x0000200008000080L});
	public static final BitSet FOLLOW_type_in_quantifier1543 = new BitSet(new long[]{0x0000000000020000L});
	public static final BitSet FOLLOW_DOUBLECOLON_in_quantifier1545 = new BitSet(new long[]{0x042000C801001000L});
	public static final BitSet FOLLOW_expression_in_quantifier1548 = new BitSet(new long[]{0x0040000000000000L});
	public static final BitSet FOLLOW_54_in_quantifier1550 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_ID_in_synpred1_Pseudo903 = new BitSet(new long[]{0x0000000000000400L});
	public static final BitSet FOLLOW_ASSIGN_in_synpred1_Pseudo905 = new BitSet(new long[]{0x0000000000004000L});
	public static final BitSet FOLLOW_CALL_in_synpred1_Pseudo907 = new BitSet(new long[]{0x0000000000000002L});
}
