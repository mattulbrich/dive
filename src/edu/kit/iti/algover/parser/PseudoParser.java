// $ANTLR 3.5.1 Pseudo.g 2015-09-09 17:25:14

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
		"CALL", "DECREASES", "DOUBLECOLON", "ELSE", "ENSURES", "EQ", "EX", "GE", 
		"GT", "ID", "IF", "IMPLIES", "INT", "INTERSECT", "INVARIANT", "LE", "LISTEX", 
		"LIT", "LT", "METHOD", "MINUS", "NOT", "OR", "PLUS", "REQUIRES", "RESULTS", 
		"RETURNS", "SET", "SETEX", "THEN", "TIMES", "UNION", "VAR", "WHILE", "WS", 
		"'('", "')'", "','", "':'", "';'", "'['", "']'"
	};
	public static final int EOF=-1;
	public static final int T__49=49;
	public static final int T__50=50;
	public static final int T__51=51;
	public static final int T__52=52;
	public static final int T__53=53;
	public static final int T__54=54;
	public static final int T__55=55;
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
	public static final int DOUBLECOLON=16;
	public static final int ELSE=17;
	public static final int ENSURES=18;
	public static final int EQ=19;
	public static final int EX=20;
	public static final int GE=21;
	public static final int GT=22;
	public static final int ID=23;
	public static final int IF=24;
	public static final int IMPLIES=25;
	public static final int INT=26;
	public static final int INTERSECT=27;
	public static final int INVARIANT=28;
	public static final int LE=29;
	public static final int LISTEX=30;
	public static final int LIT=31;
	public static final int LT=32;
	public static final int METHOD=33;
	public static final int MINUS=34;
	public static final int NOT=35;
	public static final int OR=36;
	public static final int PLUS=37;
	public static final int REQUIRES=38;
	public static final int RESULTS=39;
	public static final int RETURNS=40;
	public static final int SET=41;
	public static final int SETEX=42;
	public static final int THEN=43;
	public static final int TIMES=44;
	public static final int UNION=45;
	public static final int VAR=46;
	public static final int WHILE=47;
	public static final int WS=48;

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
	// Pseudo.g:101:1: program : ( method )+ ;
	public final PseudoParser.program_return program() throws RecognitionException {
		PseudoParser.program_return retval = new PseudoParser.program_return();
		retval.start = input.LT(1);

		PseudoTree root_0 = null;

		ParserRuleReturnScope method1 =null;


		try {
			// Pseudo.g:101:8: ( ( method )+ )
			// Pseudo.g:102:3: ( method )+
			{
			root_0 = (PseudoTree)adaptor.nil();


			// Pseudo.g:102:3: ( method )+
			int cnt1=0;
			loop1:
			while (true) {
				int alt1=2;
				int LA1_0 = input.LA(1);
				if ( (LA1_0==METHOD) ) {
					alt1=1;
				}

				switch (alt1) {
				case 1 :
					// Pseudo.g:102:3: method
					{
					pushFollow(FOLLOW_method_in_program403);
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
	// Pseudo.g:105:1: method : 'method' ID '(' ( vars )? ')' ( returns_ )? ( requires )* ( ensures )* ( decreases )? '{' ( decl )* ( statements )? '}' -> ^( 'method' ID ^( ARGS ( vars )? ) ( returns_ )? ( requires )* ( ensures )* ( decreases )? ( decl )* ^( BLOCK ( statements )? ) ) ;
	public final PseudoParser.method_return method() throws RecognitionException {
		PseudoParser.method_return retval = new PseudoParser.method_return();
		retval.start = input.LT(1);

		PseudoTree root_0 = null;

		Token string_literal2=null;
		Token ID3=null;
		Token char_literal4=null;
		Token char_literal6=null;
		Token char_literal11=null;
		Token char_literal14=null;
		ParserRuleReturnScope vars5 =null;
		ParserRuleReturnScope returns_7 =null;
		ParserRuleReturnScope requires8 =null;
		ParserRuleReturnScope ensures9 =null;
		ParserRuleReturnScope decreases10 =null;
		ParserRuleReturnScope decl12 =null;
		ParserRuleReturnScope statements13 =null;

		PseudoTree string_literal2_tree=null;
		PseudoTree ID3_tree=null;
		PseudoTree char_literal4_tree=null;
		PseudoTree char_literal6_tree=null;
		PseudoTree char_literal11_tree=null;
		PseudoTree char_literal14_tree=null;
		RewriteRuleTokenStream stream_49=new RewriteRuleTokenStream(adaptor,"token 49");
		RewriteRuleTokenStream stream_ID=new RewriteRuleTokenStream(adaptor,"token ID");
		RewriteRuleTokenStream stream_BLOCK_BEGIN=new RewriteRuleTokenStream(adaptor,"token BLOCK_BEGIN");
		RewriteRuleTokenStream stream_METHOD=new RewriteRuleTokenStream(adaptor,"token METHOD");
		RewriteRuleTokenStream stream_BLOCK_END=new RewriteRuleTokenStream(adaptor,"token BLOCK_END");
		RewriteRuleTokenStream stream_50=new RewriteRuleTokenStream(adaptor,"token 50");
		RewriteRuleSubtreeStream stream_returns_=new RewriteRuleSubtreeStream(adaptor,"rule returns_");
		RewriteRuleSubtreeStream stream_ensures=new RewriteRuleSubtreeStream(adaptor,"rule ensures");
		RewriteRuleSubtreeStream stream_vars=new RewriteRuleSubtreeStream(adaptor,"rule vars");
		RewriteRuleSubtreeStream stream_decreases=new RewriteRuleSubtreeStream(adaptor,"rule decreases");
		RewriteRuleSubtreeStream stream_statements=new RewriteRuleSubtreeStream(adaptor,"rule statements");
		RewriteRuleSubtreeStream stream_requires=new RewriteRuleSubtreeStream(adaptor,"rule requires");
		RewriteRuleSubtreeStream stream_decl=new RewriteRuleSubtreeStream(adaptor,"rule decl");

		try {
			// Pseudo.g:105:7: ( 'method' ID '(' ( vars )? ')' ( returns_ )? ( requires )* ( ensures )* ( decreases )? '{' ( decl )* ( statements )? '}' -> ^( 'method' ID ^( ARGS ( vars )? ) ( returns_ )? ( requires )* ( ensures )* ( decreases )? ( decl )* ^( BLOCK ( statements )? ) ) )
			// Pseudo.g:106:3: 'method' ID '(' ( vars )? ')' ( returns_ )? ( requires )* ( ensures )* ( decreases )? '{' ( decl )* ( statements )? '}'
			{
			string_literal2=(Token)match(input,METHOD,FOLLOW_METHOD_in_method417); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_METHOD.add(string_literal2);

			ID3=(Token)match(input,ID,FOLLOW_ID_in_method419); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_ID.add(ID3);

			char_literal4=(Token)match(input,49,FOLLOW_49_in_method421); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_49.add(char_literal4);

			// Pseudo.g:106:19: ( vars )?
			int alt2=2;
			int LA2_0 = input.LA(1);
			if ( (LA2_0==ID) ) {
				alt2=1;
			}
			switch (alt2) {
				case 1 :
					// Pseudo.g:106:19: vars
					{
					pushFollow(FOLLOW_vars_in_method423);
					vars5=vars();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_vars.add(vars5.getTree());
					}
					break;

			}

			char_literal6=(Token)match(input,50,FOLLOW_50_in_method426); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_50.add(char_literal6);

			// Pseudo.g:107:3: ( returns_ )?
			int alt3=2;
			int LA3_0 = input.LA(1);
			if ( (LA3_0==RETURNS) ) {
				alt3=1;
			}
			switch (alt3) {
				case 1 :
					// Pseudo.g:107:5: returns_
					{
					pushFollow(FOLLOW_returns__in_method432);
					returns_7=returns_();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_returns_.add(returns_7.getTree());
					}
					break;

			}

			// Pseudo.g:108:3: ( requires )*
			loop4:
			while (true) {
				int alt4=2;
				int LA4_0 = input.LA(1);
				if ( (LA4_0==REQUIRES) ) {
					alt4=1;
				}

				switch (alt4) {
				case 1 :
					// Pseudo.g:108:5: requires
					{
					pushFollow(FOLLOW_requires_in_method441);
					requires8=requires();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_requires.add(requires8.getTree());
					}
					break;

				default :
					break loop4;
				}
			}

			// Pseudo.g:109:3: ( ensures )*
			loop5:
			while (true) {
				int alt5=2;
				int LA5_0 = input.LA(1);
				if ( (LA5_0==ENSURES) ) {
					alt5=1;
				}

				switch (alt5) {
				case 1 :
					// Pseudo.g:109:5: ensures
					{
					pushFollow(FOLLOW_ensures_in_method450);
					ensures9=ensures();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_ensures.add(ensures9.getTree());
					}
					break;

				default :
					break loop5;
				}
			}

			// Pseudo.g:110:3: ( decreases )?
			int alt6=2;
			int LA6_0 = input.LA(1);
			if ( (LA6_0==DECREASES) ) {
				alt6=1;
			}
			switch (alt6) {
				case 1 :
					// Pseudo.g:110:5: decreases
					{
					pushFollow(FOLLOW_decreases_in_method459);
					decreases10=decreases();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_decreases.add(decreases10.getTree());
					}
					break;

			}

			char_literal11=(Token)match(input,BLOCK_BEGIN,FOLLOW_BLOCK_BEGIN_in_method466); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_BLOCK_BEGIN.add(char_literal11);

			// Pseudo.g:111:7: ( decl )*
			loop7:
			while (true) {
				int alt7=2;
				int LA7_0 = input.LA(1);
				if ( (LA7_0==VAR) ) {
					alt7=1;
				}

				switch (alt7) {
				case 1 :
					// Pseudo.g:111:9: decl
					{
					pushFollow(FOLLOW_decl_in_method470);
					decl12=decl();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_decl.add(decl12.getTree());
					}
					break;

				default :
					break loop7;
				}
			}

			// Pseudo.g:111:17: ( statements )?
			int alt8=2;
			int LA8_0 = input.LA(1);
			if ( (LA8_0==ASSERT||(LA8_0 >= ID && LA8_0 <= IF)||LA8_0==WHILE) ) {
				alt8=1;
			}
			switch (alt8) {
				case 1 :
					// Pseudo.g:111:17: statements
					{
					pushFollow(FOLLOW_statements_in_method475);
					statements13=statements();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_statements.add(statements13.getTree());
					}
					break;

			}

			char_literal14=(Token)match(input,BLOCK_END,FOLLOW_BLOCK_END_in_method478); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_BLOCK_END.add(char_literal14);

			// AST REWRITE
			// elements: ensures, requires, ID, decreases, statements, returns_, decl, vars, METHOD
			// token labels: 
			// rule labels: retval
			// token list labels: 
			// rule list labels: 
			// wildcard labels: 
			if ( state.backtracking==0 ) {
			retval.tree = root_0;
			RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

			root_0 = (PseudoTree)adaptor.nil();
			// 112:3: -> ^( 'method' ID ^( ARGS ( vars )? ) ( returns_ )? ( requires )* ( ensures )* ( decreases )? ( decl )* ^( BLOCK ( statements )? ) )
			{
				// Pseudo.g:113:5: ^( 'method' ID ^( ARGS ( vars )? ) ( returns_ )? ( requires )* ( ensures )* ( decreases )? ( decl )* ^( BLOCK ( statements )? ) )
				{
				PseudoTree root_1 = (PseudoTree)adaptor.nil();
				root_1 = (PseudoTree)adaptor.becomeRoot(stream_METHOD.nextNode(), root_1);
				adaptor.addChild(root_1, stream_ID.nextNode());
				// Pseudo.g:113:19: ^( ARGS ( vars )? )
				{
				PseudoTree root_2 = (PseudoTree)adaptor.nil();
				root_2 = (PseudoTree)adaptor.becomeRoot((PseudoTree)adaptor.create(ARGS, "ARGS"), root_2);
				// Pseudo.g:113:26: ( vars )?
				if ( stream_vars.hasNext() ) {
					adaptor.addChild(root_2, stream_vars.nextTree());
				}
				stream_vars.reset();

				adaptor.addChild(root_1, root_2);
				}

				// Pseudo.g:113:33: ( returns_ )?
				if ( stream_returns_.hasNext() ) {
					adaptor.addChild(root_1, stream_returns_.nextTree());
				}
				stream_returns_.reset();

				// Pseudo.g:113:43: ( requires )*
				while ( stream_requires.hasNext() ) {
					adaptor.addChild(root_1, stream_requires.nextTree());
				}
				stream_requires.reset();

				// Pseudo.g:113:53: ( ensures )*
				while ( stream_ensures.hasNext() ) {
					adaptor.addChild(root_1, stream_ensures.nextTree());
				}
				stream_ensures.reset();

				// Pseudo.g:114:9: ( decreases )?
				if ( stream_decreases.hasNext() ) {
					adaptor.addChild(root_1, stream_decreases.nextTree());
				}
				stream_decreases.reset();

				// Pseudo.g:114:20: ( decl )*
				while ( stream_decl.hasNext() ) {
					adaptor.addChild(root_1, stream_decl.nextTree());
				}
				stream_decl.reset();

				// Pseudo.g:114:26: ^( BLOCK ( statements )? )
				{
				PseudoTree root_2 = (PseudoTree)adaptor.nil();
				root_2 = (PseudoTree)adaptor.becomeRoot((PseudoTree)adaptor.create(BLOCK, "BLOCK"), root_2);
				// Pseudo.g:114:34: ( statements )?
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
	// Pseudo.g:117:1: decl : VAR ! var ';' !;
	public final PseudoParser.decl_return decl() throws RecognitionException {
		PseudoParser.decl_return retval = new PseudoParser.decl_return();
		retval.start = input.LT(1);

		PseudoTree root_0 = null;

		Token VAR15=null;
		Token char_literal17=null;
		ParserRuleReturnScope var16 =null;

		PseudoTree VAR15_tree=null;
		PseudoTree char_literal17_tree=null;

		try {
			// Pseudo.g:117:5: ( VAR ! var ';' !)
			// Pseudo.g:118:3: VAR ! var ';' !
			{
			root_0 = (PseudoTree)adaptor.nil();


			VAR15=(Token)match(input,VAR,FOLLOW_VAR_in_decl542); if (state.failed) return retval;
			pushFollow(FOLLOW_var_in_decl545);
			var16=var();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, var16.getTree());

			char_literal17=(Token)match(input,53,FOLLOW_53_in_decl547); if (state.failed) return retval;
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
	// Pseudo.g:121:1: vars : var ( ',' ! var )* ;
	public final PseudoParser.vars_return vars() throws RecognitionException {
		PseudoParser.vars_return retval = new PseudoParser.vars_return();
		retval.start = input.LT(1);

		PseudoTree root_0 = null;

		Token char_literal19=null;
		ParserRuleReturnScope var18 =null;
		ParserRuleReturnScope var20 =null;

		PseudoTree char_literal19_tree=null;

		try {
			// Pseudo.g:121:5: ( var ( ',' ! var )* )
			// Pseudo.g:122:3: var ( ',' ! var )*
			{
			root_0 = (PseudoTree)adaptor.nil();


			pushFollow(FOLLOW_var_in_vars560);
			var18=var();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, var18.getTree());

			// Pseudo.g:123:3: ( ',' ! var )*
			loop9:
			while (true) {
				int alt9=2;
				int LA9_0 = input.LA(1);
				if ( (LA9_0==51) ) {
					alt9=1;
				}

				switch (alt9) {
				case 1 :
					// Pseudo.g:123:5: ',' ! var
					{
					char_literal19=(Token)match(input,51,FOLLOW_51_in_vars566); if (state.failed) return retval;
					pushFollow(FOLLOW_var_in_vars569);
					var20=var();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, var20.getTree());

					}
					break;

				default :
					break loop9;
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
	// Pseudo.g:126:1: var : ID ':' type -> ^( VAR ID type ) ;
	public final PseudoParser.var_return var() throws RecognitionException {
		PseudoParser.var_return retval = new PseudoParser.var_return();
		retval.start = input.LT(1);

		PseudoTree root_0 = null;

		Token ID21=null;
		Token char_literal22=null;
		ParserRuleReturnScope type23 =null;

		PseudoTree ID21_tree=null;
		PseudoTree char_literal22_tree=null;
		RewriteRuleTokenStream stream_ID=new RewriteRuleTokenStream(adaptor,"token ID");
		RewriteRuleTokenStream stream_52=new RewriteRuleTokenStream(adaptor,"token 52");
		RewriteRuleSubtreeStream stream_type=new RewriteRuleSubtreeStream(adaptor,"rule type");

		try {
			// Pseudo.g:126:4: ( ID ':' type -> ^( VAR ID type ) )
			// Pseudo.g:127:3: ID ':' type
			{
			ID21=(Token)match(input,ID,FOLLOW_ID_in_var584); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_ID.add(ID21);

			char_literal22=(Token)match(input,52,FOLLOW_52_in_var586); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_52.add(char_literal22);

			pushFollow(FOLLOW_type_in_var588);
			type23=type();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) stream_type.add(type23.getTree());
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

			root_0 = (PseudoTree)adaptor.nil();
			// 127:15: -> ^( VAR ID type )
			{
				// Pseudo.g:127:18: ^( VAR ID type )
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
	// Pseudo.g:130:1: type : ( INT | SET ^ '<' ! INT '>' !| ARRAY ^ '<' ! INT '>' !);
	public final PseudoParser.type_return type() throws RecognitionException {
		PseudoParser.type_return retval = new PseudoParser.type_return();
		retval.start = input.LT(1);

		PseudoTree root_0 = null;

		Token INT24=null;
		Token SET25=null;
		Token char_literal26=null;
		Token INT27=null;
		Token char_literal28=null;
		Token ARRAY29=null;
		Token char_literal30=null;
		Token INT31=null;
		Token char_literal32=null;

		PseudoTree INT24_tree=null;
		PseudoTree SET25_tree=null;
		PseudoTree char_literal26_tree=null;
		PseudoTree INT27_tree=null;
		PseudoTree char_literal28_tree=null;
		PseudoTree ARRAY29_tree=null;
		PseudoTree char_literal30_tree=null;
		PseudoTree INT31_tree=null;
		PseudoTree char_literal32_tree=null;

		try {
			// Pseudo.g:130:5: ( INT | SET ^ '<' ! INT '>' !| ARRAY ^ '<' ! INT '>' !)
			int alt10=3;
			switch ( input.LA(1) ) {
			case INT:
				{
				alt10=1;
				}
				break;
			case SET:
				{
				alt10=2;
				}
				break;
			case ARRAY:
				{
				alt10=3;
				}
				break;
			default:
				if (state.backtracking>0) {state.failed=true; return retval;}
				NoViableAltException nvae =
					new NoViableAltException("", 10, 0, input);
				throw nvae;
			}
			switch (alt10) {
				case 1 :
					// Pseudo.g:131:5: INT
					{
					root_0 = (PseudoTree)adaptor.nil();


					INT24=(Token)match(input,INT,FOLLOW_INT_in_type612); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					INT24_tree = (PseudoTree)adaptor.create(INT24);
					adaptor.addChild(root_0, INT24_tree);
					}

					}
					break;
				case 2 :
					// Pseudo.g:131:11: SET ^ '<' ! INT '>' !
					{
					root_0 = (PseudoTree)adaptor.nil();


					SET25=(Token)match(input,SET,FOLLOW_SET_in_type616); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					SET25_tree = (PseudoTree)adaptor.create(SET25);
					root_0 = (PseudoTree)adaptor.becomeRoot(SET25_tree, root_0);
					}

					char_literal26=(Token)match(input,LT,FOLLOW_LT_in_type619); if (state.failed) return retval;
					INT27=(Token)match(input,INT,FOLLOW_INT_in_type622); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					INT27_tree = (PseudoTree)adaptor.create(INT27);
					adaptor.addChild(root_0, INT27_tree);
					}

					char_literal28=(Token)match(input,GT,FOLLOW_GT_in_type624); if (state.failed) return retval;
					}
					break;
				case 3 :
					// Pseudo.g:132:5: ARRAY ^ '<' ! INT '>' !
					{
					root_0 = (PseudoTree)adaptor.nil();


					ARRAY29=(Token)match(input,ARRAY,FOLLOW_ARRAY_in_type631); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					ARRAY29_tree = (PseudoTree)adaptor.create(ARRAY29);
					root_0 = (PseudoTree)adaptor.becomeRoot(ARRAY29_tree, root_0);
					}

					char_literal30=(Token)match(input,LT,FOLLOW_LT_in_type634); if (state.failed) return retval;
					INT31=(Token)match(input,INT,FOLLOW_INT_in_type637); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					INT31_tree = (PseudoTree)adaptor.create(INT31);
					adaptor.addChild(root_0, INT31_tree);
					}

					char_literal32=(Token)match(input,GT,FOLLOW_GT_in_type639); if (state.failed) return retval;
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
	// Pseudo.g:135:1: returns_ : RETURNS ^ '(' ! vars ')' !;
	public final PseudoParser.returns__return returns_() throws RecognitionException {
		PseudoParser.returns__return retval = new PseudoParser.returns__return();
		retval.start = input.LT(1);

		PseudoTree root_0 = null;

		Token RETURNS33=null;
		Token char_literal34=null;
		Token char_literal36=null;
		ParserRuleReturnScope vars35 =null;

		PseudoTree RETURNS33_tree=null;
		PseudoTree char_literal34_tree=null;
		PseudoTree char_literal36_tree=null;

		try {
			// Pseudo.g:135:9: ( RETURNS ^ '(' ! vars ')' !)
			// Pseudo.g:136:3: RETURNS ^ '(' ! vars ')' !
			{
			root_0 = (PseudoTree)adaptor.nil();


			RETURNS33=(Token)match(input,RETURNS,FOLLOW_RETURNS_in_returns_652); if (state.failed) return retval;
			if ( state.backtracking==0 ) {
			RETURNS33_tree = (PseudoTree)adaptor.create(RETURNS33);
			root_0 = (PseudoTree)adaptor.becomeRoot(RETURNS33_tree, root_0);
			}

			char_literal34=(Token)match(input,49,FOLLOW_49_in_returns_655); if (state.failed) return retval;
			pushFollow(FOLLOW_vars_in_returns_658);
			vars35=vars();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, vars35.getTree());

			char_literal36=(Token)match(input,50,FOLLOW_50_in_returns_660); if (state.failed) return retval;
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
	// Pseudo.g:139:1: requires : REQUIRES ^ ( ID ':' !)? expression ;
	public final PseudoParser.requires_return requires() throws RecognitionException {
		PseudoParser.requires_return retval = new PseudoParser.requires_return();
		retval.start = input.LT(1);

		PseudoTree root_0 = null;

		Token REQUIRES37=null;
		Token ID38=null;
		Token char_literal39=null;
		ParserRuleReturnScope expression40 =null;

		PseudoTree REQUIRES37_tree=null;
		PseudoTree ID38_tree=null;
		PseudoTree char_literal39_tree=null;

		try {
			// Pseudo.g:139:9: ( REQUIRES ^ ( ID ':' !)? expression )
			// Pseudo.g:140:3: REQUIRES ^ ( ID ':' !)? expression
			{
			root_0 = (PseudoTree)adaptor.nil();


			REQUIRES37=(Token)match(input,REQUIRES,FOLLOW_REQUIRES_in_requires673); if (state.failed) return retval;
			if ( state.backtracking==0 ) {
			REQUIRES37_tree = (PseudoTree)adaptor.create(REQUIRES37);
			root_0 = (PseudoTree)adaptor.becomeRoot(REQUIRES37_tree, root_0);
			}

			// Pseudo.g:140:13: ( ID ':' !)?
			int alt11=2;
			int LA11_0 = input.LA(1);
			if ( (LA11_0==ID) ) {
				int LA11_1 = input.LA(2);
				if ( (LA11_1==52) ) {
					alt11=1;
				}
			}
			switch (alt11) {
				case 1 :
					// Pseudo.g:140:14: ID ':' !
					{
					ID38=(Token)match(input,ID,FOLLOW_ID_in_requires677); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					ID38_tree = (PseudoTree)adaptor.create(ID38);
					adaptor.addChild(root_0, ID38_tree);
					}

					char_literal39=(Token)match(input,52,FOLLOW_52_in_requires679); if (state.failed) return retval;
					}
					break;

			}

			pushFollow(FOLLOW_expression_in_requires684);
			expression40=expression();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, expression40.getTree());

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
	// Pseudo.g:143:1: ensures : ENSURES ^ ( ID ':' !)? expression ;
	public final PseudoParser.ensures_return ensures() throws RecognitionException {
		PseudoParser.ensures_return retval = new PseudoParser.ensures_return();
		retval.start = input.LT(1);

		PseudoTree root_0 = null;

		Token ENSURES41=null;
		Token ID42=null;
		Token char_literal43=null;
		ParserRuleReturnScope expression44 =null;

		PseudoTree ENSURES41_tree=null;
		PseudoTree ID42_tree=null;
		PseudoTree char_literal43_tree=null;

		try {
			// Pseudo.g:143:8: ( ENSURES ^ ( ID ':' !)? expression )
			// Pseudo.g:144:3: ENSURES ^ ( ID ':' !)? expression
			{
			root_0 = (PseudoTree)adaptor.nil();


			ENSURES41=(Token)match(input,ENSURES,FOLLOW_ENSURES_in_ensures696); if (state.failed) return retval;
			if ( state.backtracking==0 ) {
			ENSURES41_tree = (PseudoTree)adaptor.create(ENSURES41);
			root_0 = (PseudoTree)adaptor.becomeRoot(ENSURES41_tree, root_0);
			}

			// Pseudo.g:144:12: ( ID ':' !)?
			int alt12=2;
			int LA12_0 = input.LA(1);
			if ( (LA12_0==ID) ) {
				int LA12_1 = input.LA(2);
				if ( (LA12_1==52) ) {
					alt12=1;
				}
			}
			switch (alt12) {
				case 1 :
					// Pseudo.g:144:13: ID ':' !
					{
					ID42=(Token)match(input,ID,FOLLOW_ID_in_ensures700); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					ID42_tree = (PseudoTree)adaptor.create(ID42);
					adaptor.addChild(root_0, ID42_tree);
					}

					char_literal43=(Token)match(input,52,FOLLOW_52_in_ensures702); if (state.failed) return retval;
					}
					break;

			}

			pushFollow(FOLLOW_expression_in_ensures707);
			expression44=expression();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, expression44.getTree());

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
	// Pseudo.g:147:1: decreases : DECREASES ^ expression ;
	public final PseudoParser.decreases_return decreases() throws RecognitionException {
		PseudoParser.decreases_return retval = new PseudoParser.decreases_return();
		retval.start = input.LT(1);

		PseudoTree root_0 = null;

		Token DECREASES45=null;
		ParserRuleReturnScope expression46 =null;

		PseudoTree DECREASES45_tree=null;

		try {
			// Pseudo.g:147:10: ( DECREASES ^ expression )
			// Pseudo.g:148:3: DECREASES ^ expression
			{
			root_0 = (PseudoTree)adaptor.nil();


			DECREASES45=(Token)match(input,DECREASES,FOLLOW_DECREASES_in_decreases719); if (state.failed) return retval;
			if ( state.backtracking==0 ) {
			DECREASES45_tree = (PseudoTree)adaptor.create(DECREASES45);
			root_0 = (PseudoTree)adaptor.becomeRoot(DECREASES45_tree, root_0);
			}

			pushFollow(FOLLOW_expression_in_decreases722);
			expression46=expression();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, expression46.getTree());

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
	// Pseudo.g:151:1: invariant : INVARIANT ^ ( ID ':' !)? expression ;
	public final PseudoParser.invariant_return invariant() throws RecognitionException {
		PseudoParser.invariant_return retval = new PseudoParser.invariant_return();
		retval.start = input.LT(1);

		PseudoTree root_0 = null;

		Token INVARIANT47=null;
		Token ID48=null;
		Token char_literal49=null;
		ParserRuleReturnScope expression50 =null;

		PseudoTree INVARIANT47_tree=null;
		PseudoTree ID48_tree=null;
		PseudoTree char_literal49_tree=null;

		try {
			// Pseudo.g:151:10: ( INVARIANT ^ ( ID ':' !)? expression )
			// Pseudo.g:152:3: INVARIANT ^ ( ID ':' !)? expression
			{
			root_0 = (PseudoTree)adaptor.nil();


			INVARIANT47=(Token)match(input,INVARIANT,FOLLOW_INVARIANT_in_invariant734); if (state.failed) return retval;
			if ( state.backtracking==0 ) {
			INVARIANT47_tree = (PseudoTree)adaptor.create(INVARIANT47);
			root_0 = (PseudoTree)adaptor.becomeRoot(INVARIANT47_tree, root_0);
			}

			// Pseudo.g:152:14: ( ID ':' !)?
			int alt13=2;
			int LA13_0 = input.LA(1);
			if ( (LA13_0==ID) ) {
				int LA13_1 = input.LA(2);
				if ( (LA13_1==52) ) {
					alt13=1;
				}
			}
			switch (alt13) {
				case 1 :
					// Pseudo.g:152:15: ID ':' !
					{
					ID48=(Token)match(input,ID,FOLLOW_ID_in_invariant738); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					ID48_tree = (PseudoTree)adaptor.create(ID48);
					adaptor.addChild(root_0, ID48_tree);
					}

					char_literal49=(Token)match(input,52,FOLLOW_52_in_invariant740); if (state.failed) return retval;
					}
					break;

			}

			pushFollow(FOLLOW_expression_in_invariant745);
			expression50=expression();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, expression50.getTree());

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
	// Pseudo.g:155:1: block : '{' ( statements )? '}' -> ^( BLOCK ( statements )? ) ;
	public final PseudoParser.block_return block() throws RecognitionException {
		PseudoParser.block_return retval = new PseudoParser.block_return();
		retval.start = input.LT(1);

		PseudoTree root_0 = null;

		Token char_literal51=null;
		Token char_literal53=null;
		ParserRuleReturnScope statements52 =null;

		PseudoTree char_literal51_tree=null;
		PseudoTree char_literal53_tree=null;
		RewriteRuleTokenStream stream_BLOCK_BEGIN=new RewriteRuleTokenStream(adaptor,"token BLOCK_BEGIN");
		RewriteRuleTokenStream stream_BLOCK_END=new RewriteRuleTokenStream(adaptor,"token BLOCK_END");
		RewriteRuleSubtreeStream stream_statements=new RewriteRuleSubtreeStream(adaptor,"rule statements");

		try {
			// Pseudo.g:155:6: ( '{' ( statements )? '}' -> ^( BLOCK ( statements )? ) )
			// Pseudo.g:156:3: '{' ( statements )? '}'
			{
			char_literal51=(Token)match(input,BLOCK_BEGIN,FOLLOW_BLOCK_BEGIN_in_block757); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_BLOCK_BEGIN.add(char_literal51);

			// Pseudo.g:156:7: ( statements )?
			int alt14=2;
			int LA14_0 = input.LA(1);
			if ( (LA14_0==ASSERT||(LA14_0 >= ID && LA14_0 <= IF)||LA14_0==WHILE) ) {
				alt14=1;
			}
			switch (alt14) {
				case 1 :
					// Pseudo.g:156:7: statements
					{
					pushFollow(FOLLOW_statements_in_block759);
					statements52=statements();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_statements.add(statements52.getTree());
					}
					break;

			}

			char_literal53=(Token)match(input,BLOCK_END,FOLLOW_BLOCK_END_in_block762); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_BLOCK_END.add(char_literal53);

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
			// 156:23: -> ^( BLOCK ( statements )? )
			{
				// Pseudo.g:156:26: ^( BLOCK ( statements )? )
				{
				PseudoTree root_1 = (PseudoTree)adaptor.nil();
				root_1 = (PseudoTree)adaptor.becomeRoot((PseudoTree)adaptor.create(BLOCK, "BLOCK"), root_1);
				// Pseudo.g:156:34: ( statements )?
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
	// Pseudo.g:159:1: relaxedBlock : ( block | statement -> ^( BLOCK statement ) );
	public final PseudoParser.relaxedBlock_return relaxedBlock() throws RecognitionException {
		PseudoParser.relaxedBlock_return retval = new PseudoParser.relaxedBlock_return();
		retval.start = input.LT(1);

		PseudoTree root_0 = null;

		ParserRuleReturnScope block54 =null;
		ParserRuleReturnScope statement55 =null;

		RewriteRuleSubtreeStream stream_statement=new RewriteRuleSubtreeStream(adaptor,"rule statement");

		try {
			// Pseudo.g:159:13: ( block | statement -> ^( BLOCK statement ) )
			int alt15=2;
			int LA15_0 = input.LA(1);
			if ( (LA15_0==BLOCK_BEGIN) ) {
				alt15=1;
			}
			else if ( (LA15_0==ASSERT||(LA15_0 >= ID && LA15_0 <= IF)||LA15_0==WHILE) ) {
				alt15=2;
			}

			else {
				if (state.backtracking>0) {state.failed=true; return retval;}
				NoViableAltException nvae =
					new NoViableAltException("", 15, 0, input);
				throw nvae;
			}

			switch (alt15) {
				case 1 :
					// Pseudo.g:160:5: block
					{
					root_0 = (PseudoTree)adaptor.nil();


					pushFollow(FOLLOW_block_in_relaxedBlock785);
					block54=block();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, block54.getTree());

					}
					break;
				case 2 :
					// Pseudo.g:161:5: statement
					{
					pushFollow(FOLLOW_statement_in_relaxedBlock791);
					statement55=statement();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_statement.add(statement55.getTree());
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
					// 161:15: -> ^( BLOCK statement )
					{
						// Pseudo.g:161:18: ^( BLOCK statement )
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
	// Pseudo.g:164:1: statements : ( statement )+ ;
	public final PseudoParser.statements_return statements() throws RecognitionException {
		PseudoParser.statements_return retval = new PseudoParser.statements_return();
		retval.start = input.LT(1);

		PseudoTree root_0 = null;

		ParserRuleReturnScope statement56 =null;


		try {
			// Pseudo.g:164:11: ( ( statement )+ )
			// Pseudo.g:165:3: ( statement )+
			{
			root_0 = (PseudoTree)adaptor.nil();


			// Pseudo.g:165:3: ( statement )+
			int cnt16=0;
			loop16:
			while (true) {
				int alt16=2;
				int LA16_0 = input.LA(1);
				if ( (LA16_0==ASSERT||(LA16_0 >= ID && LA16_0 <= IF)||LA16_0==WHILE) ) {
					alt16=1;
				}

				switch (alt16) {
				case 1 :
					// Pseudo.g:165:5: statement
					{
					pushFollow(FOLLOW_statement_in_statements813);
					statement56=statement();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, statement56.getTree());

					}
					break;

				default :
					if ( cnt16 >= 1 ) break loop16;
					if (state.backtracking>0) {state.failed=true; return retval;}
					EarlyExitException eee = new EarlyExitException(16, input);
					throw eee;
				}
				cnt16++;
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
	// Pseudo.g:168:1: statement : ( ID ':=' ^ expression ';' !| ( ID ':=' 'call' )=>r= ID ':=' 'call' f= ID '(' ( expressions )? ')' ';' -> ^( 'call' $f ^( RESULTS $r) ^( ARGS ( expressions )? ) ) | ids ':=' 'call' ID '(' ( expressions )? ')' ';' -> ^( 'call' ID ^( RESULTS ids ) ^( ARGS ( expressions )? ) ) | 'while' ^ expression ( invariant )+ decreases relaxedBlock | 'if' ^ expression relaxedBlock ( options {greedy=true; } : 'else' ! relaxedBlock )? | 'assert' ^ ( ID ':' !)? expression ';' !);
	public final PseudoParser.statement_return statement() throws RecognitionException {
		PseudoParser.statement_return retval = new PseudoParser.statement_return();
		retval.start = input.LT(1);

		PseudoTree root_0 = null;

		Token r=null;
		Token f=null;
		Token ID57=null;
		Token string_literal58=null;
		Token char_literal60=null;
		Token string_literal61=null;
		Token string_literal62=null;
		Token char_literal63=null;
		Token char_literal65=null;
		Token char_literal66=null;
		Token string_literal68=null;
		Token string_literal69=null;
		Token ID70=null;
		Token char_literal71=null;
		Token char_literal73=null;
		Token char_literal74=null;
		Token string_literal75=null;
		Token string_literal80=null;
		Token string_literal83=null;
		Token string_literal85=null;
		Token ID86=null;
		Token char_literal87=null;
		Token char_literal89=null;
		ParserRuleReturnScope expression59 =null;
		ParserRuleReturnScope expressions64 =null;
		ParserRuleReturnScope ids67 =null;
		ParserRuleReturnScope expressions72 =null;
		ParserRuleReturnScope expression76 =null;
		ParserRuleReturnScope invariant77 =null;
		ParserRuleReturnScope decreases78 =null;
		ParserRuleReturnScope relaxedBlock79 =null;
		ParserRuleReturnScope expression81 =null;
		ParserRuleReturnScope relaxedBlock82 =null;
		ParserRuleReturnScope relaxedBlock84 =null;
		ParserRuleReturnScope expression88 =null;

		PseudoTree r_tree=null;
		PseudoTree f_tree=null;
		PseudoTree ID57_tree=null;
		PseudoTree string_literal58_tree=null;
		PseudoTree char_literal60_tree=null;
		PseudoTree string_literal61_tree=null;
		PseudoTree string_literal62_tree=null;
		PseudoTree char_literal63_tree=null;
		PseudoTree char_literal65_tree=null;
		PseudoTree char_literal66_tree=null;
		PseudoTree string_literal68_tree=null;
		PseudoTree string_literal69_tree=null;
		PseudoTree ID70_tree=null;
		PseudoTree char_literal71_tree=null;
		PseudoTree char_literal73_tree=null;
		PseudoTree char_literal74_tree=null;
		PseudoTree string_literal75_tree=null;
		PseudoTree string_literal80_tree=null;
		PseudoTree string_literal83_tree=null;
		PseudoTree string_literal85_tree=null;
		PseudoTree ID86_tree=null;
		PseudoTree char_literal87_tree=null;
		PseudoTree char_literal89_tree=null;
		RewriteRuleTokenStream stream_49=new RewriteRuleTokenStream(adaptor,"token 49");
		RewriteRuleTokenStream stream_CALL=new RewriteRuleTokenStream(adaptor,"token CALL");
		RewriteRuleTokenStream stream_ID=new RewriteRuleTokenStream(adaptor,"token ID");
		RewriteRuleTokenStream stream_53=new RewriteRuleTokenStream(adaptor,"token 53");
		RewriteRuleTokenStream stream_50=new RewriteRuleTokenStream(adaptor,"token 50");
		RewriteRuleTokenStream stream_ASSIGN=new RewriteRuleTokenStream(adaptor,"token ASSIGN");
		RewriteRuleSubtreeStream stream_ids=new RewriteRuleSubtreeStream(adaptor,"rule ids");
		RewriteRuleSubtreeStream stream_expressions=new RewriteRuleSubtreeStream(adaptor,"rule expressions");

		try {
			// Pseudo.g:168:10: ( ID ':=' ^ expression ';' !| ( ID ':=' 'call' )=>r= ID ':=' 'call' f= ID '(' ( expressions )? ')' ';' -> ^( 'call' $f ^( RESULTS $r) ^( ARGS ( expressions )? ) ) | ids ':=' 'call' ID '(' ( expressions )? ')' ';' -> ^( 'call' ID ^( RESULTS ids ) ^( ARGS ( expressions )? ) ) | 'while' ^ expression ( invariant )+ decreases relaxedBlock | 'if' ^ expression relaxedBlock ( options {greedy=true; } : 'else' ! relaxedBlock )? | 'assert' ^ ( ID ':' !)? expression ';' !)
			int alt22=6;
			switch ( input.LA(1) ) {
			case ID:
				{
				int LA22_1 = input.LA(2);
				if ( (LA22_1==ASSIGN) ) {
					int LA22_5 = input.LA(3);
					if ( (LA22_5==CALL) && (synpred1_Pseudo())) {
						alt22=2;
					}
					else if ( (LA22_5==BLOCK_BEGIN||LA22_5==ID||LA22_5==LIT||(LA22_5 >= MINUS && LA22_5 <= NOT)||LA22_5==49||LA22_5==54) ) {
						alt22=1;
					}

					else {
						if (state.backtracking>0) {state.failed=true; return retval;}
						int nvaeMark = input.mark();
						try {
							for (int nvaeConsume = 0; nvaeConsume < 3 - 1; nvaeConsume++) {
								input.consume();
							}
							NoViableAltException nvae =
								new NoViableAltException("", 22, 5, input);
							throw nvae;
						} finally {
							input.rewind(nvaeMark);
						}
					}

				}
				else if ( (LA22_1==51) ) {
					alt22=3;
				}

				else {
					if (state.backtracking>0) {state.failed=true; return retval;}
					int nvaeMark = input.mark();
					try {
						input.consume();
						NoViableAltException nvae =
							new NoViableAltException("", 22, 1, input);
						throw nvae;
					} finally {
						input.rewind(nvaeMark);
					}
				}

				}
				break;
			case WHILE:
				{
				alt22=4;
				}
				break;
			case IF:
				{
				alt22=5;
				}
				break;
			case ASSERT:
				{
				alt22=6;
				}
				break;
			default:
				if (state.backtracking>0) {state.failed=true; return retval;}
				NoViableAltException nvae =
					new NoViableAltException("", 22, 0, input);
				throw nvae;
			}
			switch (alt22) {
				case 1 :
					// Pseudo.g:169:5: ID ':=' ^ expression ';' !
					{
					root_0 = (PseudoTree)adaptor.nil();


					ID57=(Token)match(input,ID,FOLLOW_ID_in_statement830); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					ID57_tree = (PseudoTree)adaptor.create(ID57);
					adaptor.addChild(root_0, ID57_tree);
					}

					string_literal58=(Token)match(input,ASSIGN,FOLLOW_ASSIGN_in_statement832); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					string_literal58_tree = (PseudoTree)adaptor.create(string_literal58);
					root_0 = (PseudoTree)adaptor.becomeRoot(string_literal58_tree, root_0);
					}

					pushFollow(FOLLOW_expression_in_statement835);
					expression59=expression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, expression59.getTree());

					char_literal60=(Token)match(input,53,FOLLOW_53_in_statement837); if (state.failed) return retval;
					}
					break;
				case 2 :
					// Pseudo.g:170:5: ( ID ':=' 'call' )=>r= ID ':=' 'call' f= ID '(' ( expressions )? ')' ';'
					{
					r=(Token)match(input,ID,FOLLOW_ID_in_statement856); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_ID.add(r);

					string_literal61=(Token)match(input,ASSIGN,FOLLOW_ASSIGN_in_statement858); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_ASSIGN.add(string_literal61);

					string_literal62=(Token)match(input,CALL,FOLLOW_CALL_in_statement860); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_CALL.add(string_literal62);

					f=(Token)match(input,ID,FOLLOW_ID_in_statement864); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_ID.add(f);

					char_literal63=(Token)match(input,49,FOLLOW_49_in_statement866); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_49.add(char_literal63);

					// Pseudo.g:170:51: ( expressions )?
					int alt17=2;
					int LA17_0 = input.LA(1);
					if ( (LA17_0==BLOCK_BEGIN||LA17_0==ID||LA17_0==LIT||(LA17_0 >= MINUS && LA17_0 <= NOT)||LA17_0==49||LA17_0==54) ) {
						alt17=1;
					}
					switch (alt17) {
						case 1 :
							// Pseudo.g:170:51: expressions
							{
							pushFollow(FOLLOW_expressions_in_statement868);
							expressions64=expressions();
							state._fsp--;
							if (state.failed) return retval;
							if ( state.backtracking==0 ) stream_expressions.add(expressions64.getTree());
							}
							break;

					}

					char_literal65=(Token)match(input,50,FOLLOW_50_in_statement871); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_50.add(char_literal65);

					char_literal66=(Token)match(input,53,FOLLOW_53_in_statement873); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_53.add(char_literal66);

					// AST REWRITE
					// elements: expressions, f, CALL, r
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
					// 171:9: -> ^( 'call' $f ^( RESULTS $r) ^( ARGS ( expressions )? ) )
					{
						// Pseudo.g:171:12: ^( 'call' $f ^( RESULTS $r) ^( ARGS ( expressions )? ) )
						{
						PseudoTree root_1 = (PseudoTree)adaptor.nil();
						root_1 = (PseudoTree)adaptor.becomeRoot(stream_CALL.nextNode(), root_1);
						adaptor.addChild(root_1, stream_f.nextNode());
						// Pseudo.g:171:24: ^( RESULTS $r)
						{
						PseudoTree root_2 = (PseudoTree)adaptor.nil();
						root_2 = (PseudoTree)adaptor.becomeRoot((PseudoTree)adaptor.create(RESULTS, "RESULTS"), root_2);
						adaptor.addChild(root_2, stream_r.nextNode());
						adaptor.addChild(root_1, root_2);
						}

						// Pseudo.g:171:38: ^( ARGS ( expressions )? )
						{
						PseudoTree root_2 = (PseudoTree)adaptor.nil();
						root_2 = (PseudoTree)adaptor.becomeRoot((PseudoTree)adaptor.create(ARGS, "ARGS"), root_2);
						// Pseudo.g:171:45: ( expressions )?
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
					// Pseudo.g:172:5: ids ':=' 'call' ID '(' ( expressions )? ')' ';'
					{
					pushFollow(FOLLOW_ids_in_statement910);
					ids67=ids();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_ids.add(ids67.getTree());
					string_literal68=(Token)match(input,ASSIGN,FOLLOW_ASSIGN_in_statement912); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_ASSIGN.add(string_literal68);

					string_literal69=(Token)match(input,CALL,FOLLOW_CALL_in_statement914); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_CALL.add(string_literal69);

					ID70=(Token)match(input,ID,FOLLOW_ID_in_statement916); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_ID.add(ID70);

					char_literal71=(Token)match(input,49,FOLLOW_49_in_statement918); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_49.add(char_literal71);

					// Pseudo.g:172:28: ( expressions )?
					int alt18=2;
					int LA18_0 = input.LA(1);
					if ( (LA18_0==BLOCK_BEGIN||LA18_0==ID||LA18_0==LIT||(LA18_0 >= MINUS && LA18_0 <= NOT)||LA18_0==49||LA18_0==54) ) {
						alt18=1;
					}
					switch (alt18) {
						case 1 :
							// Pseudo.g:172:28: expressions
							{
							pushFollow(FOLLOW_expressions_in_statement920);
							expressions72=expressions();
							state._fsp--;
							if (state.failed) return retval;
							if ( state.backtracking==0 ) stream_expressions.add(expressions72.getTree());
							}
							break;

					}

					char_literal73=(Token)match(input,50,FOLLOW_50_in_statement923); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_50.add(char_literal73);

					char_literal74=(Token)match(input,53,FOLLOW_53_in_statement925); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_53.add(char_literal74);

					// AST REWRITE
					// elements: CALL, ids, expressions, ID
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (PseudoTree)adaptor.nil();
					// 173:9: -> ^( 'call' ID ^( RESULTS ids ) ^( ARGS ( expressions )? ) )
					{
						// Pseudo.g:173:12: ^( 'call' ID ^( RESULTS ids ) ^( ARGS ( expressions )? ) )
						{
						PseudoTree root_1 = (PseudoTree)adaptor.nil();
						root_1 = (PseudoTree)adaptor.becomeRoot(stream_CALL.nextNode(), root_1);
						adaptor.addChild(root_1, stream_ID.nextNode());
						// Pseudo.g:173:24: ^( RESULTS ids )
						{
						PseudoTree root_2 = (PseudoTree)adaptor.nil();
						root_2 = (PseudoTree)adaptor.becomeRoot((PseudoTree)adaptor.create(RESULTS, "RESULTS"), root_2);
						adaptor.addChild(root_2, stream_ids.nextTree());
						adaptor.addChild(root_1, root_2);
						}

						// Pseudo.g:173:39: ^( ARGS ( expressions )? )
						{
						PseudoTree root_2 = (PseudoTree)adaptor.nil();
						root_2 = (PseudoTree)adaptor.becomeRoot((PseudoTree)adaptor.create(ARGS, "ARGS"), root_2);
						// Pseudo.g:173:46: ( expressions )?
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
					// Pseudo.g:174:5: 'while' ^ expression ( invariant )+ decreases relaxedBlock
					{
					root_0 = (PseudoTree)adaptor.nil();


					string_literal75=(Token)match(input,WHILE,FOLLOW_WHILE_in_statement960); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					string_literal75_tree = (PseudoTree)adaptor.create(string_literal75);
					root_0 = (PseudoTree)adaptor.becomeRoot(string_literal75_tree, root_0);
					}

					pushFollow(FOLLOW_expression_in_statement963);
					expression76=expression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, expression76.getTree());

					// Pseudo.g:175:7: ( invariant )+
					int cnt19=0;
					loop19:
					while (true) {
						int alt19=2;
						int LA19_0 = input.LA(1);
						if ( (LA19_0==INVARIANT) ) {
							alt19=1;
						}

						switch (alt19) {
						case 1 :
							// Pseudo.g:175:7: invariant
							{
							pushFollow(FOLLOW_invariant_in_statement971);
							invariant77=invariant();
							state._fsp--;
							if (state.failed) return retval;
							if ( state.backtracking==0 ) adaptor.addChild(root_0, invariant77.getTree());

							}
							break;

						default :
							if ( cnt19 >= 1 ) break loop19;
							if (state.backtracking>0) {state.failed=true; return retval;}
							EarlyExitException eee = new EarlyExitException(19, input);
							throw eee;
						}
						cnt19++;
					}

					pushFollow(FOLLOW_decreases_in_statement980);
					decreases78=decreases();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, decreases78.getTree());

					pushFollow(FOLLOW_relaxedBlock_in_statement988);
					relaxedBlock79=relaxedBlock();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, relaxedBlock79.getTree());

					}
					break;
				case 5 :
					// Pseudo.g:178:5: 'if' ^ expression relaxedBlock ( options {greedy=true; } : 'else' ! relaxedBlock )?
					{
					root_0 = (PseudoTree)adaptor.nil();


					string_literal80=(Token)match(input,IF,FOLLOW_IF_in_statement994); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					string_literal80_tree = (PseudoTree)adaptor.create(string_literal80);
					root_0 = (PseudoTree)adaptor.becomeRoot(string_literal80_tree, root_0);
					}

					pushFollow(FOLLOW_expression_in_statement997);
					expression81=expression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, expression81.getTree());

					pushFollow(FOLLOW_relaxedBlock_in_statement999);
					relaxedBlock82=relaxedBlock();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, relaxedBlock82.getTree());

					// Pseudo.g:179:7: ( options {greedy=true; } : 'else' ! relaxedBlock )?
					int alt20=2;
					int LA20_0 = input.LA(1);
					if ( (LA20_0==ELSE) ) {
						alt20=1;
					}
					switch (alt20) {
						case 1 :
							// Pseudo.g:179:36: 'else' ! relaxedBlock
							{
							string_literal83=(Token)match(input,ELSE,FOLLOW_ELSE_in_statement1020); if (state.failed) return retval;
							pushFollow(FOLLOW_relaxedBlock_in_statement1023);
							relaxedBlock84=relaxedBlock();
							state._fsp--;
							if (state.failed) return retval;
							if ( state.backtracking==0 ) adaptor.addChild(root_0, relaxedBlock84.getTree());

							}
							break;

					}

					}
					break;
				case 6 :
					// Pseudo.g:180:5: 'assert' ^ ( ID ':' !)? expression ';' !
					{
					root_0 = (PseudoTree)adaptor.nil();


					string_literal85=(Token)match(input,ASSERT,FOLLOW_ASSERT_in_statement1032); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					string_literal85_tree = (PseudoTree)adaptor.create(string_literal85);
					root_0 = (PseudoTree)adaptor.becomeRoot(string_literal85_tree, root_0);
					}

					// Pseudo.g:180:15: ( ID ':' !)?
					int alt21=2;
					int LA21_0 = input.LA(1);
					if ( (LA21_0==ID) ) {
						int LA21_1 = input.LA(2);
						if ( (LA21_1==52) ) {
							alt21=1;
						}
					}
					switch (alt21) {
						case 1 :
							// Pseudo.g:180:17: ID ':' !
							{
							ID86=(Token)match(input,ID,FOLLOW_ID_in_statement1037); if (state.failed) return retval;
							if ( state.backtracking==0 ) {
							ID86_tree = (PseudoTree)adaptor.create(ID86);
							adaptor.addChild(root_0, ID86_tree);
							}

							char_literal87=(Token)match(input,52,FOLLOW_52_in_statement1039); if (state.failed) return retval;
							}
							break;

					}

					pushFollow(FOLLOW_expression_in_statement1045);
					expression88=expression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, expression88.getTree());

					char_literal89=(Token)match(input,53,FOLLOW_53_in_statement1047); if (state.failed) return retval;
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
	// Pseudo.g:183:1: ids : ID ( ',' ! ID )+ ;
	public final PseudoParser.ids_return ids() throws RecognitionException {
		PseudoParser.ids_return retval = new PseudoParser.ids_return();
		retval.start = input.LT(1);

		PseudoTree root_0 = null;

		Token ID90=null;
		Token char_literal91=null;
		Token ID92=null;

		PseudoTree ID90_tree=null;
		PseudoTree char_literal91_tree=null;
		PseudoTree ID92_tree=null;

		try {
			// Pseudo.g:183:4: ( ID ( ',' ! ID )+ )
			// Pseudo.g:184:3: ID ( ',' ! ID )+
			{
			root_0 = (PseudoTree)adaptor.nil();


			ID90=(Token)match(input,ID,FOLLOW_ID_in_ids1060); if (state.failed) return retval;
			if ( state.backtracking==0 ) {
			ID90_tree = (PseudoTree)adaptor.create(ID90);
			adaptor.addChild(root_0, ID90_tree);
			}

			// Pseudo.g:184:6: ( ',' ! ID )+
			int cnt23=0;
			loop23:
			while (true) {
				int alt23=2;
				int LA23_0 = input.LA(1);
				if ( (LA23_0==51) ) {
					alt23=1;
				}

				switch (alt23) {
				case 1 :
					// Pseudo.g:184:7: ',' ! ID
					{
					char_literal91=(Token)match(input,51,FOLLOW_51_in_ids1063); if (state.failed) return retval;
					ID92=(Token)match(input,ID,FOLLOW_ID_in_ids1066); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					ID92_tree = (PseudoTree)adaptor.create(ID92);
					adaptor.addChild(root_0, ID92_tree);
					}

					}
					break;

				default :
					if ( cnt23 >= 1 ) break loop23;
					if (state.backtracking>0) {state.failed=true; return retval;}
					EarlyExitException eee = new EarlyExitException(23, input);
					throw eee;
				}
				cnt23++;
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
	// Pseudo.g:187:1: expressions : expression ( ',' ! expression )* ;
	public final PseudoParser.expressions_return expressions() throws RecognitionException {
		PseudoParser.expressions_return retval = new PseudoParser.expressions_return();
		retval.start = input.LT(1);

		PseudoTree root_0 = null;

		Token char_literal94=null;
		ParserRuleReturnScope expression93 =null;
		ParserRuleReturnScope expression95 =null;

		PseudoTree char_literal94_tree=null;

		try {
			// Pseudo.g:187:12: ( expression ( ',' ! expression )* )
			// Pseudo.g:188:3: expression ( ',' ! expression )*
			{
			root_0 = (PseudoTree)adaptor.nil();


			pushFollow(FOLLOW_expression_in_expressions1080);
			expression93=expression();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, expression93.getTree());

			// Pseudo.g:188:14: ( ',' ! expression )*
			loop24:
			while (true) {
				int alt24=2;
				int LA24_0 = input.LA(1);
				if ( (LA24_0==51) ) {
					alt24=1;
				}

				switch (alt24) {
				case 1 :
					// Pseudo.g:188:16: ',' ! expression
					{
					char_literal94=(Token)match(input,51,FOLLOW_51_in_expressions1084); if (state.failed) return retval;
					pushFollow(FOLLOW_expression_in_expressions1087);
					expression95=expression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, expression95.getTree());

					}
					break;

				default :
					break loop24;
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
	// Pseudo.g:191:1: expression : or_expr ;
	public final PseudoParser.expression_return expression() throws RecognitionException {
		PseudoParser.expression_return retval = new PseudoParser.expression_return();
		retval.start = input.LT(1);

		PseudoTree root_0 = null;

		ParserRuleReturnScope or_expr96 =null;


		try {
			// Pseudo.g:191:11: ( or_expr )
			// Pseudo.g:192:3: or_expr
			{
			root_0 = (PseudoTree)adaptor.nil();


			pushFollow(FOLLOW_or_expr_in_expression1102);
			or_expr96=or_expr();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, or_expr96.getTree());

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
	// Pseudo.g:194:1: or_expr : and_expr ( ( '||' ^| '==>' ^) or_expr )? ;
	public final PseudoParser.or_expr_return or_expr() throws RecognitionException {
		PseudoParser.or_expr_return retval = new PseudoParser.or_expr_return();
		retval.start = input.LT(1);

		PseudoTree root_0 = null;

		Token string_literal98=null;
		Token string_literal99=null;
		ParserRuleReturnScope and_expr97 =null;
		ParserRuleReturnScope or_expr100 =null;

		PseudoTree string_literal98_tree=null;
		PseudoTree string_literal99_tree=null;

		try {
			// Pseudo.g:194:8: ( and_expr ( ( '||' ^| '==>' ^) or_expr )? )
			// Pseudo.g:195:3: and_expr ( ( '||' ^| '==>' ^) or_expr )?
			{
			root_0 = (PseudoTree)adaptor.nil();


			pushFollow(FOLLOW_and_expr_in_or_expr1111);
			and_expr97=and_expr();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, and_expr97.getTree());

			// Pseudo.g:195:12: ( ( '||' ^| '==>' ^) or_expr )?
			int alt26=2;
			int LA26_0 = input.LA(1);
			if ( (LA26_0==IMPLIES||LA26_0==OR) ) {
				alt26=1;
			}
			switch (alt26) {
				case 1 :
					// Pseudo.g:195:14: ( '||' ^| '==>' ^) or_expr
					{
					// Pseudo.g:195:14: ( '||' ^| '==>' ^)
					int alt25=2;
					int LA25_0 = input.LA(1);
					if ( (LA25_0==OR) ) {
						alt25=1;
					}
					else if ( (LA25_0==IMPLIES) ) {
						alt25=2;
					}

					else {
						if (state.backtracking>0) {state.failed=true; return retval;}
						NoViableAltException nvae =
							new NoViableAltException("", 25, 0, input);
						throw nvae;
					}

					switch (alt25) {
						case 1 :
							// Pseudo.g:195:15: '||' ^
							{
							string_literal98=(Token)match(input,OR,FOLLOW_OR_in_or_expr1116); if (state.failed) return retval;
							if ( state.backtracking==0 ) {
							string_literal98_tree = (PseudoTree)adaptor.create(string_literal98);
							root_0 = (PseudoTree)adaptor.becomeRoot(string_literal98_tree, root_0);
							}

							}
							break;
						case 2 :
							// Pseudo.g:195:23: '==>' ^
							{
							string_literal99=(Token)match(input,IMPLIES,FOLLOW_IMPLIES_in_or_expr1121); if (state.failed) return retval;
							if ( state.backtracking==0 ) {
							string_literal99_tree = (PseudoTree)adaptor.create(string_literal99);
							root_0 = (PseudoTree)adaptor.becomeRoot(string_literal99_tree, root_0);
							}

							}
							break;

					}

					pushFollow(FOLLOW_or_expr_in_or_expr1125);
					or_expr100=or_expr();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, or_expr100.getTree());

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
	// Pseudo.g:198:1: and_expr : rel_expr ( '&&' ^ and_expr )? ;
	public final PseudoParser.and_expr_return and_expr() throws RecognitionException {
		PseudoParser.and_expr_return retval = new PseudoParser.and_expr_return();
		retval.start = input.LT(1);

		PseudoTree root_0 = null;

		Token string_literal102=null;
		ParserRuleReturnScope rel_expr101 =null;
		ParserRuleReturnScope and_expr103 =null;

		PseudoTree string_literal102_tree=null;

		try {
			// Pseudo.g:198:9: ( rel_expr ( '&&' ^ and_expr )? )
			// Pseudo.g:199:3: rel_expr ( '&&' ^ and_expr )?
			{
			root_0 = (PseudoTree)adaptor.nil();


			pushFollow(FOLLOW_rel_expr_in_and_expr1140);
			rel_expr101=rel_expr();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, rel_expr101.getTree());

			// Pseudo.g:199:12: ( '&&' ^ and_expr )?
			int alt27=2;
			int LA27_0 = input.LA(1);
			if ( (LA27_0==AND) ) {
				alt27=1;
			}
			switch (alt27) {
				case 1 :
					// Pseudo.g:199:14: '&&' ^ and_expr
					{
					string_literal102=(Token)match(input,AND,FOLLOW_AND_in_and_expr1144); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					string_literal102_tree = (PseudoTree)adaptor.create(string_literal102);
					root_0 = (PseudoTree)adaptor.becomeRoot(string_literal102_tree, root_0);
					}

					pushFollow(FOLLOW_and_expr_in_and_expr1147);
					and_expr103=and_expr();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, and_expr103.getTree());

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
	// Pseudo.g:202:1: rel_expr : add_expr ( ( '<' ^| '>' ^| '==' ^| '<=' ^| '>=' ^) add_expr )? ;
	public final PseudoParser.rel_expr_return rel_expr() throws RecognitionException {
		PseudoParser.rel_expr_return retval = new PseudoParser.rel_expr_return();
		retval.start = input.LT(1);

		PseudoTree root_0 = null;

		Token char_literal105=null;
		Token char_literal106=null;
		Token string_literal107=null;
		Token string_literal108=null;
		Token string_literal109=null;
		ParserRuleReturnScope add_expr104 =null;
		ParserRuleReturnScope add_expr110 =null;

		PseudoTree char_literal105_tree=null;
		PseudoTree char_literal106_tree=null;
		PseudoTree string_literal107_tree=null;
		PseudoTree string_literal108_tree=null;
		PseudoTree string_literal109_tree=null;

		try {
			// Pseudo.g:202:9: ( add_expr ( ( '<' ^| '>' ^| '==' ^| '<=' ^| '>=' ^) add_expr )? )
			// Pseudo.g:203:3: add_expr ( ( '<' ^| '>' ^| '==' ^| '<=' ^| '>=' ^) add_expr )?
			{
			root_0 = (PseudoTree)adaptor.nil();


			pushFollow(FOLLOW_add_expr_in_rel_expr1162);
			add_expr104=add_expr();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, add_expr104.getTree());

			// Pseudo.g:203:12: ( ( '<' ^| '>' ^| '==' ^| '<=' ^| '>=' ^) add_expr )?
			int alt29=2;
			int LA29_0 = input.LA(1);
			if ( (LA29_0==EQ||(LA29_0 >= GE && LA29_0 <= GT)||LA29_0==LE||LA29_0==LT) ) {
				alt29=1;
			}
			switch (alt29) {
				case 1 :
					// Pseudo.g:203:14: ( '<' ^| '>' ^| '==' ^| '<=' ^| '>=' ^) add_expr
					{
					// Pseudo.g:203:14: ( '<' ^| '>' ^| '==' ^| '<=' ^| '>=' ^)
					int alt28=5;
					switch ( input.LA(1) ) {
					case LT:
						{
						alt28=1;
						}
						break;
					case GT:
						{
						alt28=2;
						}
						break;
					case EQ:
						{
						alt28=3;
						}
						break;
					case LE:
						{
						alt28=4;
						}
						break;
					case GE:
						{
						alt28=5;
						}
						break;
					default:
						if (state.backtracking>0) {state.failed=true; return retval;}
						NoViableAltException nvae =
							new NoViableAltException("", 28, 0, input);
						throw nvae;
					}
					switch (alt28) {
						case 1 :
							// Pseudo.g:203:15: '<' ^
							{
							char_literal105=(Token)match(input,LT,FOLLOW_LT_in_rel_expr1167); if (state.failed) return retval;
							if ( state.backtracking==0 ) {
							char_literal105_tree = (PseudoTree)adaptor.create(char_literal105);
							root_0 = (PseudoTree)adaptor.becomeRoot(char_literal105_tree, root_0);
							}

							}
							break;
						case 2 :
							// Pseudo.g:203:22: '>' ^
							{
							char_literal106=(Token)match(input,GT,FOLLOW_GT_in_rel_expr1172); if (state.failed) return retval;
							if ( state.backtracking==0 ) {
							char_literal106_tree = (PseudoTree)adaptor.create(char_literal106);
							root_0 = (PseudoTree)adaptor.becomeRoot(char_literal106_tree, root_0);
							}

							}
							break;
						case 3 :
							// Pseudo.g:203:29: '==' ^
							{
							string_literal107=(Token)match(input,EQ,FOLLOW_EQ_in_rel_expr1177); if (state.failed) return retval;
							if ( state.backtracking==0 ) {
							string_literal107_tree = (PseudoTree)adaptor.create(string_literal107);
							root_0 = (PseudoTree)adaptor.becomeRoot(string_literal107_tree, root_0);
							}

							}
							break;
						case 4 :
							// Pseudo.g:203:37: '<=' ^
							{
							string_literal108=(Token)match(input,LE,FOLLOW_LE_in_rel_expr1182); if (state.failed) return retval;
							if ( state.backtracking==0 ) {
							string_literal108_tree = (PseudoTree)adaptor.create(string_literal108);
							root_0 = (PseudoTree)adaptor.becomeRoot(string_literal108_tree, root_0);
							}

							}
							break;
						case 5 :
							// Pseudo.g:203:45: '>=' ^
							{
							string_literal109=(Token)match(input,GE,FOLLOW_GE_in_rel_expr1187); if (state.failed) return retval;
							if ( state.backtracking==0 ) {
							string_literal109_tree = (PseudoTree)adaptor.create(string_literal109);
							root_0 = (PseudoTree)adaptor.becomeRoot(string_literal109_tree, root_0);
							}

							}
							break;

					}

					pushFollow(FOLLOW_add_expr_in_rel_expr1191);
					add_expr110=add_expr();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, add_expr110.getTree());

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
	// Pseudo.g:206:1: add_expr : mul_expr ( ( '+' | '-' | '++' ) ^ add_expr )? ;
	public final PseudoParser.add_expr_return add_expr() throws RecognitionException {
		PseudoParser.add_expr_return retval = new PseudoParser.add_expr_return();
		retval.start = input.LT(1);

		PseudoTree root_0 = null;

		Token set112=null;
		ParserRuleReturnScope mul_expr111 =null;
		ParserRuleReturnScope add_expr113 =null;

		PseudoTree set112_tree=null;

		try {
			// Pseudo.g:206:9: ( mul_expr ( ( '+' | '-' | '++' ) ^ add_expr )? )
			// Pseudo.g:207:3: mul_expr ( ( '+' | '-' | '++' ) ^ add_expr )?
			{
			root_0 = (PseudoTree)adaptor.nil();


			pushFollow(FOLLOW_mul_expr_in_add_expr1206);
			mul_expr111=mul_expr();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, mul_expr111.getTree());

			// Pseudo.g:207:12: ( ( '+' | '-' | '++' ) ^ add_expr )?
			int alt30=2;
			int LA30_0 = input.LA(1);
			if ( (LA30_0==MINUS||LA30_0==PLUS||LA30_0==UNION) ) {
				alt30=1;
			}
			switch (alt30) {
				case 1 :
					// Pseudo.g:207:14: ( '+' | '-' | '++' ) ^ add_expr
					{
					set112=input.LT(1);
					set112=input.LT(1);
					if ( input.LA(1)==MINUS||input.LA(1)==PLUS||input.LA(1)==UNION ) {
						input.consume();
						if ( state.backtracking==0 ) root_0 = (PseudoTree)adaptor.becomeRoot((PseudoTree)adaptor.create(set112), root_0);
						state.errorRecovery=false;
						state.failed=false;
					}
					else {
						if (state.backtracking>0) {state.failed=true; return retval;}
						MismatchedSetException mse = new MismatchedSetException(null,input);
						throw mse;
					}
					pushFollow(FOLLOW_add_expr_in_add_expr1223);
					add_expr113=add_expr();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, add_expr113.getTree());

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
	// Pseudo.g:210:1: mul_expr : prefix_expr ( ( '*' | '**' ) ^ mul_expr )? ;
	public final PseudoParser.mul_expr_return mul_expr() throws RecognitionException {
		PseudoParser.mul_expr_return retval = new PseudoParser.mul_expr_return();
		retval.start = input.LT(1);

		PseudoTree root_0 = null;

		Token set115=null;
		ParserRuleReturnScope prefix_expr114 =null;
		ParserRuleReturnScope mul_expr116 =null;

		PseudoTree set115_tree=null;

		try {
			// Pseudo.g:210:9: ( prefix_expr ( ( '*' | '**' ) ^ mul_expr )? )
			// Pseudo.g:211:3: prefix_expr ( ( '*' | '**' ) ^ mul_expr )?
			{
			root_0 = (PseudoTree)adaptor.nil();


			pushFollow(FOLLOW_prefix_expr_in_mul_expr1238);
			prefix_expr114=prefix_expr();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, prefix_expr114.getTree());

			// Pseudo.g:211:15: ( ( '*' | '**' ) ^ mul_expr )?
			int alt31=2;
			int LA31_0 = input.LA(1);
			if ( (LA31_0==INTERSECT||LA31_0==TIMES) ) {
				alt31=1;
			}
			switch (alt31) {
				case 1 :
					// Pseudo.g:211:17: ( '*' | '**' ) ^ mul_expr
					{
					set115=input.LT(1);
					set115=input.LT(1);
					if ( input.LA(1)==INTERSECT||input.LA(1)==TIMES ) {
						input.consume();
						if ( state.backtracking==0 ) root_0 = (PseudoTree)adaptor.becomeRoot((PseudoTree)adaptor.create(set115), root_0);
						state.errorRecovery=false;
						state.failed=false;
					}
					else {
						if (state.backtracking>0) {state.failed=true; return retval;}
						MismatchedSetException mse = new MismatchedSetException(null,input);
						throw mse;
					}
					pushFollow(FOLLOW_mul_expr_in_mul_expr1251);
					mul_expr116=mul_expr();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, mul_expr116.getTree());

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
	// Pseudo.g:214:1: prefix_expr : ( '-' ^ prefix_expr | '!' ^ prefix_expr | postfix_expr );
	public final PseudoParser.prefix_expr_return prefix_expr() throws RecognitionException {
		PseudoParser.prefix_expr_return retval = new PseudoParser.prefix_expr_return();
		retval.start = input.LT(1);

		PseudoTree root_0 = null;

		Token char_literal117=null;
		Token char_literal119=null;
		ParserRuleReturnScope prefix_expr118 =null;
		ParserRuleReturnScope prefix_expr120 =null;
		ParserRuleReturnScope postfix_expr121 =null;

		PseudoTree char_literal117_tree=null;
		PseudoTree char_literal119_tree=null;

		try {
			// Pseudo.g:214:12: ( '-' ^ prefix_expr | '!' ^ prefix_expr | postfix_expr )
			int alt32=3;
			switch ( input.LA(1) ) {
			case MINUS:
				{
				alt32=1;
				}
				break;
			case NOT:
				{
				alt32=2;
				}
				break;
			case BLOCK_BEGIN:
			case ID:
			case LIT:
			case 49:
			case 54:
				{
				alt32=3;
				}
				break;
			default:
				if (state.backtracking>0) {state.failed=true; return retval;}
				NoViableAltException nvae =
					new NoViableAltException("", 32, 0, input);
				throw nvae;
			}
			switch (alt32) {
				case 1 :
					// Pseudo.g:215:5: '-' ^ prefix_expr
					{
					root_0 = (PseudoTree)adaptor.nil();


					char_literal117=(Token)match(input,MINUS,FOLLOW_MINUS_in_prefix_expr1268); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					char_literal117_tree = (PseudoTree)adaptor.create(char_literal117);
					root_0 = (PseudoTree)adaptor.becomeRoot(char_literal117_tree, root_0);
					}

					pushFollow(FOLLOW_prefix_expr_in_prefix_expr1271);
					prefix_expr118=prefix_expr();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, prefix_expr118.getTree());

					}
					break;
				case 2 :
					// Pseudo.g:216:5: '!' ^ prefix_expr
					{
					root_0 = (PseudoTree)adaptor.nil();


					char_literal119=(Token)match(input,NOT,FOLLOW_NOT_in_prefix_expr1277); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					char_literal119_tree = (PseudoTree)adaptor.create(char_literal119);
					root_0 = (PseudoTree)adaptor.becomeRoot(char_literal119_tree, root_0);
					}

					pushFollow(FOLLOW_prefix_expr_in_prefix_expr1280);
					prefix_expr120=prefix_expr();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, prefix_expr120.getTree());

					}
					break;
				case 3 :
					// Pseudo.g:217:5: postfix_expr
					{
					root_0 = (PseudoTree)adaptor.nil();


					pushFollow(FOLLOW_postfix_expr_in_prefix_expr1286);
					postfix_expr121=postfix_expr();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, postfix_expr121.getTree());

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
	// Pseudo.g:220:1: postfix_expr : atom_expr ( '[' expression ']' -> ^( ARRAY_ACCESS atom_expr expression ) | -> atom_expr ) ;
	public final PseudoParser.postfix_expr_return postfix_expr() throws RecognitionException {
		PseudoParser.postfix_expr_return retval = new PseudoParser.postfix_expr_return();
		retval.start = input.LT(1);

		PseudoTree root_0 = null;

		Token char_literal123=null;
		Token char_literal125=null;
		ParserRuleReturnScope atom_expr122 =null;
		ParserRuleReturnScope expression124 =null;

		PseudoTree char_literal123_tree=null;
		PseudoTree char_literal125_tree=null;
		RewriteRuleTokenStream stream_55=new RewriteRuleTokenStream(adaptor,"token 55");
		RewriteRuleTokenStream stream_54=new RewriteRuleTokenStream(adaptor,"token 54");
		RewriteRuleSubtreeStream stream_expression=new RewriteRuleSubtreeStream(adaptor,"rule expression");
		RewriteRuleSubtreeStream stream_atom_expr=new RewriteRuleSubtreeStream(adaptor,"rule atom_expr");

		try {
			// Pseudo.g:220:13: ( atom_expr ( '[' expression ']' -> ^( ARRAY_ACCESS atom_expr expression ) | -> atom_expr ) )
			// Pseudo.g:221:3: atom_expr ( '[' expression ']' -> ^( ARRAY_ACCESS atom_expr expression ) | -> atom_expr )
			{
			pushFollow(FOLLOW_atom_expr_in_postfix_expr1298);
			atom_expr122=atom_expr();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) stream_atom_expr.add(atom_expr122.getTree());
			// Pseudo.g:222:3: ( '[' expression ']' -> ^( ARRAY_ACCESS atom_expr expression ) | -> atom_expr )
			int alt33=2;
			int LA33_0 = input.LA(1);
			if ( (LA33_0==54) ) {
				alt33=1;
			}
			else if ( (LA33_0==AND||LA33_0==ASSERT||(LA33_0 >= BLOCK_BEGIN && LA33_0 <= BLOCK_END)||LA33_0==DECREASES||(LA33_0 >= ENSURES && LA33_0 <= EQ)||(LA33_0 >= GE && LA33_0 <= IMPLIES)||(LA33_0 >= INTERSECT && LA33_0 <= LE)||LA33_0==LT||LA33_0==MINUS||(LA33_0 >= OR && LA33_0 <= REQUIRES)||(LA33_0 >= TIMES && LA33_0 <= UNION)||LA33_0==WHILE||(LA33_0 >= 50 && LA33_0 <= 51)||LA33_0==53||LA33_0==55) ) {
				alt33=2;
			}

			else {
				if (state.backtracking>0) {state.failed=true; return retval;}
				NoViableAltException nvae =
					new NoViableAltException("", 33, 0, input);
				throw nvae;
			}

			switch (alt33) {
				case 1 :
					// Pseudo.g:222:5: '[' expression ']'
					{
					char_literal123=(Token)match(input,54,FOLLOW_54_in_postfix_expr1304); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_54.add(char_literal123);

					pushFollow(FOLLOW_expression_in_postfix_expr1306);
					expression124=expression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_expression.add(expression124.getTree());
					char_literal125=(Token)match(input,55,FOLLOW_55_in_postfix_expr1308); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_55.add(char_literal125);

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

					root_0 = (PseudoTree)adaptor.nil();
					// 222:24: -> ^( ARRAY_ACCESS atom_expr expression )
					{
						// Pseudo.g:222:27: ^( ARRAY_ACCESS atom_expr expression )
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
					// Pseudo.g:223:5: 
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
					// 223:5: -> atom_expr
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
	// Pseudo.g:226:1: atom_expr : ( ID | LIT | quantifier | '(' ! expression ')' !| '{' ( expressions )? '}' -> ^( SETEX ( expressions )? ) | '[' ( expressions )? ']' -> ^( LISTEX ( expressions )? ) );
	public final PseudoParser.atom_expr_return atom_expr() throws RecognitionException {
		PseudoParser.atom_expr_return retval = new PseudoParser.atom_expr_return();
		retval.start = input.LT(1);

		PseudoTree root_0 = null;

		Token ID126=null;
		Token LIT127=null;
		Token char_literal129=null;
		Token char_literal131=null;
		Token char_literal132=null;
		Token char_literal134=null;
		Token char_literal135=null;
		Token char_literal137=null;
		ParserRuleReturnScope quantifier128 =null;
		ParserRuleReturnScope expression130 =null;
		ParserRuleReturnScope expressions133 =null;
		ParserRuleReturnScope expressions136 =null;

		PseudoTree ID126_tree=null;
		PseudoTree LIT127_tree=null;
		PseudoTree char_literal129_tree=null;
		PseudoTree char_literal131_tree=null;
		PseudoTree char_literal132_tree=null;
		PseudoTree char_literal134_tree=null;
		PseudoTree char_literal135_tree=null;
		PseudoTree char_literal137_tree=null;
		RewriteRuleTokenStream stream_55=new RewriteRuleTokenStream(adaptor,"token 55");
		RewriteRuleTokenStream stream_BLOCK_BEGIN=new RewriteRuleTokenStream(adaptor,"token BLOCK_BEGIN");
		RewriteRuleTokenStream stream_54=new RewriteRuleTokenStream(adaptor,"token 54");
		RewriteRuleTokenStream stream_BLOCK_END=new RewriteRuleTokenStream(adaptor,"token BLOCK_END");
		RewriteRuleSubtreeStream stream_expressions=new RewriteRuleSubtreeStream(adaptor,"rule expressions");

		try {
			// Pseudo.g:226:10: ( ID | LIT | quantifier | '(' ! expression ')' !| '{' ( expressions )? '}' -> ^( SETEX ( expressions )? ) | '[' ( expressions )? ']' -> ^( LISTEX ( expressions )? ) )
			int alt36=6;
			switch ( input.LA(1) ) {
			case ID:
				{
				alt36=1;
				}
				break;
			case LIT:
				{
				alt36=2;
				}
				break;
			case 49:
				{
				int LA36_3 = input.LA(2);
				if ( (LA36_3==ALL||LA36_3==EX) ) {
					alt36=3;
				}
				else if ( (LA36_3==BLOCK_BEGIN||LA36_3==ID||LA36_3==LIT||(LA36_3 >= MINUS && LA36_3 <= NOT)||LA36_3==49||LA36_3==54) ) {
					alt36=4;
				}

				else {
					if (state.backtracking>0) {state.failed=true; return retval;}
					int nvaeMark = input.mark();
					try {
						input.consume();
						NoViableAltException nvae =
							new NoViableAltException("", 36, 3, input);
						throw nvae;
					} finally {
						input.rewind(nvaeMark);
					}
				}

				}
				break;
			case BLOCK_BEGIN:
				{
				alt36=5;
				}
				break;
			case 54:
				{
				alt36=6;
				}
				break;
			default:
				if (state.backtracking>0) {state.failed=true; return retval;}
				NoViableAltException nvae =
					new NoViableAltException("", 36, 0, input);
				throw nvae;
			}
			switch (alt36) {
				case 1 :
					// Pseudo.g:227:5: ID
					{
					root_0 = (PseudoTree)adaptor.nil();


					ID126=(Token)match(input,ID,FOLLOW_ID_in_atom_expr1343); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					ID126_tree = (PseudoTree)adaptor.create(ID126);
					adaptor.addChild(root_0, ID126_tree);
					}

					}
					break;
				case 2 :
					// Pseudo.g:228:5: LIT
					{
					root_0 = (PseudoTree)adaptor.nil();


					LIT127=(Token)match(input,LIT,FOLLOW_LIT_in_atom_expr1349); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					LIT127_tree = (PseudoTree)adaptor.create(LIT127);
					adaptor.addChild(root_0, LIT127_tree);
					}

					}
					break;
				case 3 :
					// Pseudo.g:229:5: quantifier
					{
					root_0 = (PseudoTree)adaptor.nil();


					pushFollow(FOLLOW_quantifier_in_atom_expr1355);
					quantifier128=quantifier();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, quantifier128.getTree());

					}
					break;
				case 4 :
					// Pseudo.g:230:5: '(' ! expression ')' !
					{
					root_0 = (PseudoTree)adaptor.nil();


					char_literal129=(Token)match(input,49,FOLLOW_49_in_atom_expr1361); if (state.failed) return retval;
					pushFollow(FOLLOW_expression_in_atom_expr1364);
					expression130=expression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, expression130.getTree());

					char_literal131=(Token)match(input,50,FOLLOW_50_in_atom_expr1366); if (state.failed) return retval;
					}
					break;
				case 5 :
					// Pseudo.g:231:5: '{' ( expressions )? '}'
					{
					char_literal132=(Token)match(input,BLOCK_BEGIN,FOLLOW_BLOCK_BEGIN_in_atom_expr1373); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_BLOCK_BEGIN.add(char_literal132);

					// Pseudo.g:231:9: ( expressions )?
					int alt34=2;
					int LA34_0 = input.LA(1);
					if ( (LA34_0==BLOCK_BEGIN||LA34_0==ID||LA34_0==LIT||(LA34_0 >= MINUS && LA34_0 <= NOT)||LA34_0==49||LA34_0==54) ) {
						alt34=1;
					}
					switch (alt34) {
						case 1 :
							// Pseudo.g:231:9: expressions
							{
							pushFollow(FOLLOW_expressions_in_atom_expr1375);
							expressions133=expressions();
							state._fsp--;
							if (state.failed) return retval;
							if ( state.backtracking==0 ) stream_expressions.add(expressions133.getTree());
							}
							break;

					}

					char_literal134=(Token)match(input,BLOCK_END,FOLLOW_BLOCK_END_in_atom_expr1378); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_BLOCK_END.add(char_literal134);

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
					// 231:26: -> ^( SETEX ( expressions )? )
					{
						// Pseudo.g:231:29: ^( SETEX ( expressions )? )
						{
						PseudoTree root_1 = (PseudoTree)adaptor.nil();
						root_1 = (PseudoTree)adaptor.becomeRoot((PseudoTree)adaptor.create(SETEX, "SETEX"), root_1);
						// Pseudo.g:231:37: ( expressions )?
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
					// Pseudo.g:232:5: '[' ( expressions )? ']'
					{
					char_literal135=(Token)match(input,54,FOLLOW_54_in_atom_expr1393); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_54.add(char_literal135);

					// Pseudo.g:232:9: ( expressions )?
					int alt35=2;
					int LA35_0 = input.LA(1);
					if ( (LA35_0==BLOCK_BEGIN||LA35_0==ID||LA35_0==LIT||(LA35_0 >= MINUS && LA35_0 <= NOT)||LA35_0==49||LA35_0==54) ) {
						alt35=1;
					}
					switch (alt35) {
						case 1 :
							// Pseudo.g:232:9: expressions
							{
							pushFollow(FOLLOW_expressions_in_atom_expr1395);
							expressions136=expressions();
							state._fsp--;
							if (state.failed) return retval;
							if ( state.backtracking==0 ) stream_expressions.add(expressions136.getTree());
							}
							break;

					}

					char_literal137=(Token)match(input,55,FOLLOW_55_in_atom_expr1398); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_55.add(char_literal137);

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
					// 232:26: -> ^( LISTEX ( expressions )? )
					{
						// Pseudo.g:232:29: ^( LISTEX ( expressions )? )
						{
						PseudoTree root_1 = (PseudoTree)adaptor.nil();
						root_1 = (PseudoTree)adaptor.becomeRoot((PseudoTree)adaptor.create(LISTEX, "LISTEX"), root_1);
						// Pseudo.g:232:38: ( expressions )?
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
	// Pseudo.g:235:1: quantifier : '(' ! ( ALL ^| EX ^) ID ':' ! type '::' ! expression ')' !;
	public final PseudoParser.quantifier_return quantifier() throws RecognitionException {
		PseudoParser.quantifier_return retval = new PseudoParser.quantifier_return();
		retval.start = input.LT(1);

		PseudoTree root_0 = null;

		Token char_literal138=null;
		Token ALL139=null;
		Token EX140=null;
		Token ID141=null;
		Token char_literal142=null;
		Token string_literal144=null;
		Token char_literal146=null;
		ParserRuleReturnScope type143 =null;
		ParserRuleReturnScope expression145 =null;

		PseudoTree char_literal138_tree=null;
		PseudoTree ALL139_tree=null;
		PseudoTree EX140_tree=null;
		PseudoTree ID141_tree=null;
		PseudoTree char_literal142_tree=null;
		PseudoTree string_literal144_tree=null;
		PseudoTree char_literal146_tree=null;

		try {
			// Pseudo.g:235:11: ( '(' ! ( ALL ^| EX ^) ID ':' ! type '::' ! expression ')' !)
			// Pseudo.g:236:3: '(' ! ( ALL ^| EX ^) ID ':' ! type '::' ! expression ')' !
			{
			root_0 = (PseudoTree)adaptor.nil();


			char_literal138=(Token)match(input,49,FOLLOW_49_in_quantifier1419); if (state.failed) return retval;
			// Pseudo.g:236:8: ( ALL ^| EX ^)
			int alt37=2;
			int LA37_0 = input.LA(1);
			if ( (LA37_0==ALL) ) {
				alt37=1;
			}
			else if ( (LA37_0==EX) ) {
				alt37=2;
			}

			else {
				if (state.backtracking>0) {state.failed=true; return retval;}
				NoViableAltException nvae =
					new NoViableAltException("", 37, 0, input);
				throw nvae;
			}

			switch (alt37) {
				case 1 :
					// Pseudo.g:236:9: ALL ^
					{
					ALL139=(Token)match(input,ALL,FOLLOW_ALL_in_quantifier1423); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					ALL139_tree = (PseudoTree)adaptor.create(ALL139);
					root_0 = (PseudoTree)adaptor.becomeRoot(ALL139_tree, root_0);
					}

					}
					break;
				case 2 :
					// Pseudo.g:236:16: EX ^
					{
					EX140=(Token)match(input,EX,FOLLOW_EX_in_quantifier1428); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					EX140_tree = (PseudoTree)adaptor.create(EX140);
					root_0 = (PseudoTree)adaptor.becomeRoot(EX140_tree, root_0);
					}

					}
					break;

			}

			ID141=(Token)match(input,ID,FOLLOW_ID_in_quantifier1432); if (state.failed) return retval;
			if ( state.backtracking==0 ) {
			ID141_tree = (PseudoTree)adaptor.create(ID141);
			adaptor.addChild(root_0, ID141_tree);
			}

			char_literal142=(Token)match(input,52,FOLLOW_52_in_quantifier1434); if (state.failed) return retval;
			pushFollow(FOLLOW_type_in_quantifier1437);
			type143=type();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, type143.getTree());

			string_literal144=(Token)match(input,DOUBLECOLON,FOLLOW_DOUBLECOLON_in_quantifier1439); if (state.failed) return retval;
			pushFollow(FOLLOW_expression_in_quantifier1442);
			expression145=expression();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, expression145.getTree());

			char_literal146=(Token)match(input,50,FOLLOW_50_in_quantifier1444); if (state.failed) return retval;
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
		// Pseudo.g:170:5: ( ID ':=' 'call' )
		// Pseudo.g:170:6: ID ':=' 'call'
		{
		match(input,ID,FOLLOW_ID_in_synpred1_Pseudo845); if (state.failed) return;

		match(input,ASSIGN,FOLLOW_ASSIGN_in_synpred1_Pseudo847); if (state.failed) return;

		match(input,CALL,FOLLOW_CALL_in_synpred1_Pseudo849); if (state.failed) return;

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



	public static final BitSet FOLLOW_method_in_program403 = new BitSet(new long[]{0x0000000200000002L});
	public static final BitSet FOLLOW_METHOD_in_method417 = new BitSet(new long[]{0x0000000000800000L});
	public static final BitSet FOLLOW_ID_in_method419 = new BitSet(new long[]{0x0002000000000000L});
	public static final BitSet FOLLOW_49_in_method421 = new BitSet(new long[]{0x0004000000800000L});
	public static final BitSet FOLLOW_vars_in_method423 = new BitSet(new long[]{0x0004000000000000L});
	public static final BitSet FOLLOW_50_in_method426 = new BitSet(new long[]{0x0000014000049000L});
	public static final BitSet FOLLOW_returns__in_method432 = new BitSet(new long[]{0x0000004000049000L});
	public static final BitSet FOLLOW_requires_in_method441 = new BitSet(new long[]{0x0000004000049000L});
	public static final BitSet FOLLOW_ensures_in_method450 = new BitSet(new long[]{0x0000000000049000L});
	public static final BitSet FOLLOW_decreases_in_method459 = new BitSet(new long[]{0x0000000000001000L});
	public static final BitSet FOLLOW_BLOCK_BEGIN_in_method466 = new BitSet(new long[]{0x0000C00001802200L});
	public static final BitSet FOLLOW_decl_in_method470 = new BitSet(new long[]{0x0000C00001802200L});
	public static final BitSet FOLLOW_statements_in_method475 = new BitSet(new long[]{0x0000000000002000L});
	public static final BitSet FOLLOW_BLOCK_END_in_method478 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_VAR_in_decl542 = new BitSet(new long[]{0x0000000000800000L});
	public static final BitSet FOLLOW_var_in_decl545 = new BitSet(new long[]{0x0020000000000000L});
	public static final BitSet FOLLOW_53_in_decl547 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_var_in_vars560 = new BitSet(new long[]{0x0008000000000002L});
	public static final BitSet FOLLOW_51_in_vars566 = new BitSet(new long[]{0x0000000000800000L});
	public static final BitSet FOLLOW_var_in_vars569 = new BitSet(new long[]{0x0008000000000002L});
	public static final BitSet FOLLOW_ID_in_var584 = new BitSet(new long[]{0x0010000000000000L});
	public static final BitSet FOLLOW_52_in_var586 = new BitSet(new long[]{0x0000020004000080L});
	public static final BitSet FOLLOW_type_in_var588 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_INT_in_type612 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_SET_in_type616 = new BitSet(new long[]{0x0000000100000000L});
	public static final BitSet FOLLOW_LT_in_type619 = new BitSet(new long[]{0x0000000004000000L});
	public static final BitSet FOLLOW_INT_in_type622 = new BitSet(new long[]{0x0000000000400000L});
	public static final BitSet FOLLOW_GT_in_type624 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_ARRAY_in_type631 = new BitSet(new long[]{0x0000000100000000L});
	public static final BitSet FOLLOW_LT_in_type634 = new BitSet(new long[]{0x0000000004000000L});
	public static final BitSet FOLLOW_INT_in_type637 = new BitSet(new long[]{0x0000000000400000L});
	public static final BitSet FOLLOW_GT_in_type639 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_RETURNS_in_returns_652 = new BitSet(new long[]{0x0002000000000000L});
	public static final BitSet FOLLOW_49_in_returns_655 = new BitSet(new long[]{0x0000000000800000L});
	public static final BitSet FOLLOW_vars_in_returns_658 = new BitSet(new long[]{0x0004000000000000L});
	public static final BitSet FOLLOW_50_in_returns_660 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_REQUIRES_in_requires673 = new BitSet(new long[]{0x0042000C80801000L});
	public static final BitSet FOLLOW_ID_in_requires677 = new BitSet(new long[]{0x0010000000000000L});
	public static final BitSet FOLLOW_52_in_requires679 = new BitSet(new long[]{0x0042000C80801000L});
	public static final BitSet FOLLOW_expression_in_requires684 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_ENSURES_in_ensures696 = new BitSet(new long[]{0x0042000C80801000L});
	public static final BitSet FOLLOW_ID_in_ensures700 = new BitSet(new long[]{0x0010000000000000L});
	public static final BitSet FOLLOW_52_in_ensures702 = new BitSet(new long[]{0x0042000C80801000L});
	public static final BitSet FOLLOW_expression_in_ensures707 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_DECREASES_in_decreases719 = new BitSet(new long[]{0x0042000C80801000L});
	public static final BitSet FOLLOW_expression_in_decreases722 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_INVARIANT_in_invariant734 = new BitSet(new long[]{0x0042000C80801000L});
	public static final BitSet FOLLOW_ID_in_invariant738 = new BitSet(new long[]{0x0010000000000000L});
	public static final BitSet FOLLOW_52_in_invariant740 = new BitSet(new long[]{0x0042000C80801000L});
	public static final BitSet FOLLOW_expression_in_invariant745 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_BLOCK_BEGIN_in_block757 = new BitSet(new long[]{0x0000800001802200L});
	public static final BitSet FOLLOW_statements_in_block759 = new BitSet(new long[]{0x0000000000002000L});
	public static final BitSet FOLLOW_BLOCK_END_in_block762 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_block_in_relaxedBlock785 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_statement_in_relaxedBlock791 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_statement_in_statements813 = new BitSet(new long[]{0x0000800001800202L});
	public static final BitSet FOLLOW_ID_in_statement830 = new BitSet(new long[]{0x0000000000000400L});
	public static final BitSet FOLLOW_ASSIGN_in_statement832 = new BitSet(new long[]{0x0042000C80801000L});
	public static final BitSet FOLLOW_expression_in_statement835 = new BitSet(new long[]{0x0020000000000000L});
	public static final BitSet FOLLOW_53_in_statement837 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_ID_in_statement856 = new BitSet(new long[]{0x0000000000000400L});
	public static final BitSet FOLLOW_ASSIGN_in_statement858 = new BitSet(new long[]{0x0000000000004000L});
	public static final BitSet FOLLOW_CALL_in_statement860 = new BitSet(new long[]{0x0000000000800000L});
	public static final BitSet FOLLOW_ID_in_statement864 = new BitSet(new long[]{0x0002000000000000L});
	public static final BitSet FOLLOW_49_in_statement866 = new BitSet(new long[]{0x0046000C80801000L});
	public static final BitSet FOLLOW_expressions_in_statement868 = new BitSet(new long[]{0x0004000000000000L});
	public static final BitSet FOLLOW_50_in_statement871 = new BitSet(new long[]{0x0020000000000000L});
	public static final BitSet FOLLOW_53_in_statement873 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_ids_in_statement910 = new BitSet(new long[]{0x0000000000000400L});
	public static final BitSet FOLLOW_ASSIGN_in_statement912 = new BitSet(new long[]{0x0000000000004000L});
	public static final BitSet FOLLOW_CALL_in_statement914 = new BitSet(new long[]{0x0000000000800000L});
	public static final BitSet FOLLOW_ID_in_statement916 = new BitSet(new long[]{0x0002000000000000L});
	public static final BitSet FOLLOW_49_in_statement918 = new BitSet(new long[]{0x0046000C80801000L});
	public static final BitSet FOLLOW_expressions_in_statement920 = new BitSet(new long[]{0x0004000000000000L});
	public static final BitSet FOLLOW_50_in_statement923 = new BitSet(new long[]{0x0020000000000000L});
	public static final BitSet FOLLOW_53_in_statement925 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_WHILE_in_statement960 = new BitSet(new long[]{0x0042000C80801000L});
	public static final BitSet FOLLOW_expression_in_statement963 = new BitSet(new long[]{0x0000000010000000L});
	public static final BitSet FOLLOW_invariant_in_statement971 = new BitSet(new long[]{0x0000000010008000L});
	public static final BitSet FOLLOW_decreases_in_statement980 = new BitSet(new long[]{0x0000800001801200L});
	public static final BitSet FOLLOW_relaxedBlock_in_statement988 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_IF_in_statement994 = new BitSet(new long[]{0x0042000C80801000L});
	public static final BitSet FOLLOW_expression_in_statement997 = new BitSet(new long[]{0x0000800001801200L});
	public static final BitSet FOLLOW_relaxedBlock_in_statement999 = new BitSet(new long[]{0x0000000000020002L});
	public static final BitSet FOLLOW_ELSE_in_statement1020 = new BitSet(new long[]{0x0000800001801200L});
	public static final BitSet FOLLOW_relaxedBlock_in_statement1023 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_ASSERT_in_statement1032 = new BitSet(new long[]{0x0042000C80801000L});
	public static final BitSet FOLLOW_ID_in_statement1037 = new BitSet(new long[]{0x0010000000000000L});
	public static final BitSet FOLLOW_52_in_statement1039 = new BitSet(new long[]{0x0042000C80801000L});
	public static final BitSet FOLLOW_expression_in_statement1045 = new BitSet(new long[]{0x0020000000000000L});
	public static final BitSet FOLLOW_53_in_statement1047 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_ID_in_ids1060 = new BitSet(new long[]{0x0008000000000000L});
	public static final BitSet FOLLOW_51_in_ids1063 = new BitSet(new long[]{0x0000000000800000L});
	public static final BitSet FOLLOW_ID_in_ids1066 = new BitSet(new long[]{0x0008000000000002L});
	public static final BitSet FOLLOW_expression_in_expressions1080 = new BitSet(new long[]{0x0008000000000002L});
	public static final BitSet FOLLOW_51_in_expressions1084 = new BitSet(new long[]{0x0042000C80801000L});
	public static final BitSet FOLLOW_expression_in_expressions1087 = new BitSet(new long[]{0x0008000000000002L});
	public static final BitSet FOLLOW_or_expr_in_expression1102 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_and_expr_in_or_expr1111 = new BitSet(new long[]{0x0000001002000002L});
	public static final BitSet FOLLOW_OR_in_or_expr1116 = new BitSet(new long[]{0x0042000C80801000L});
	public static final BitSet FOLLOW_IMPLIES_in_or_expr1121 = new BitSet(new long[]{0x0042000C80801000L});
	public static final BitSet FOLLOW_or_expr_in_or_expr1125 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_rel_expr_in_and_expr1140 = new BitSet(new long[]{0x0000000000000022L});
	public static final BitSet FOLLOW_AND_in_and_expr1144 = new BitSet(new long[]{0x0042000C80801000L});
	public static final BitSet FOLLOW_and_expr_in_and_expr1147 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_add_expr_in_rel_expr1162 = new BitSet(new long[]{0x0000000120680002L});
	public static final BitSet FOLLOW_LT_in_rel_expr1167 = new BitSet(new long[]{0x0042000C80801000L});
	public static final BitSet FOLLOW_GT_in_rel_expr1172 = new BitSet(new long[]{0x0042000C80801000L});
	public static final BitSet FOLLOW_EQ_in_rel_expr1177 = new BitSet(new long[]{0x0042000C80801000L});
	public static final BitSet FOLLOW_LE_in_rel_expr1182 = new BitSet(new long[]{0x0042000C80801000L});
	public static final BitSet FOLLOW_GE_in_rel_expr1187 = new BitSet(new long[]{0x0042000C80801000L});
	public static final BitSet FOLLOW_add_expr_in_rel_expr1191 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_mul_expr_in_add_expr1206 = new BitSet(new long[]{0x0000202400000002L});
	public static final BitSet FOLLOW_set_in_add_expr1210 = new BitSet(new long[]{0x0042000C80801000L});
	public static final BitSet FOLLOW_add_expr_in_add_expr1223 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_prefix_expr_in_mul_expr1238 = new BitSet(new long[]{0x0000100008000002L});
	public static final BitSet FOLLOW_set_in_mul_expr1242 = new BitSet(new long[]{0x0042000C80801000L});
	public static final BitSet FOLLOW_mul_expr_in_mul_expr1251 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_MINUS_in_prefix_expr1268 = new BitSet(new long[]{0x0042000C80801000L});
	public static final BitSet FOLLOW_prefix_expr_in_prefix_expr1271 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_NOT_in_prefix_expr1277 = new BitSet(new long[]{0x0042000C80801000L});
	public static final BitSet FOLLOW_prefix_expr_in_prefix_expr1280 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_postfix_expr_in_prefix_expr1286 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_atom_expr_in_postfix_expr1298 = new BitSet(new long[]{0x0040000000000002L});
	public static final BitSet FOLLOW_54_in_postfix_expr1304 = new BitSet(new long[]{0x0042000C80801000L});
	public static final BitSet FOLLOW_expression_in_postfix_expr1306 = new BitSet(new long[]{0x0080000000000000L});
	public static final BitSet FOLLOW_55_in_postfix_expr1308 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_ID_in_atom_expr1343 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_LIT_in_atom_expr1349 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_quantifier_in_atom_expr1355 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_49_in_atom_expr1361 = new BitSet(new long[]{0x0042000C80801000L});
	public static final BitSet FOLLOW_expression_in_atom_expr1364 = new BitSet(new long[]{0x0004000000000000L});
	public static final BitSet FOLLOW_50_in_atom_expr1366 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_BLOCK_BEGIN_in_atom_expr1373 = new BitSet(new long[]{0x0042000C80803000L});
	public static final BitSet FOLLOW_expressions_in_atom_expr1375 = new BitSet(new long[]{0x0000000000002000L});
	public static final BitSet FOLLOW_BLOCK_END_in_atom_expr1378 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_54_in_atom_expr1393 = new BitSet(new long[]{0x00C2000C80801000L});
	public static final BitSet FOLLOW_expressions_in_atom_expr1395 = new BitSet(new long[]{0x0080000000000000L});
	public static final BitSet FOLLOW_55_in_atom_expr1398 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_49_in_quantifier1419 = new BitSet(new long[]{0x0000000000100010L});
	public static final BitSet FOLLOW_ALL_in_quantifier1423 = new BitSet(new long[]{0x0000000000800000L});
	public static final BitSet FOLLOW_EX_in_quantifier1428 = new BitSet(new long[]{0x0000000000800000L});
	public static final BitSet FOLLOW_ID_in_quantifier1432 = new BitSet(new long[]{0x0010000000000000L});
	public static final BitSet FOLLOW_52_in_quantifier1434 = new BitSet(new long[]{0x0000020004000080L});
	public static final BitSet FOLLOW_type_in_quantifier1437 = new BitSet(new long[]{0x0000000000010000L});
	public static final BitSet FOLLOW_DOUBLECOLON_in_quantifier1439 = new BitSet(new long[]{0x0042000C80801000L});
	public static final BitSet FOLLOW_expression_in_quantifier1442 = new BitSet(new long[]{0x0004000000000000L});
	public static final BitSet FOLLOW_50_in_quantifier1444 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_ID_in_synpred1_Pseudo845 = new BitSet(new long[]{0x0000000000000400L});
	public static final BitSet FOLLOW_ASSIGN_in_synpred1_Pseudo847 = new BitSet(new long[]{0x0000000000004000L});
	public static final BitSet FOLLOW_CALL_in_synpred1_Pseudo849 = new BitSet(new long[]{0x0000000000000002L});
}
