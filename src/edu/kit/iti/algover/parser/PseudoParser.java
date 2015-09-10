// $ANTLR 3.5.1 Pseudo.g 2015-09-10 12:11:29

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
		"GE", "GT", "ID", "IF", "IMPLIES", "INT", "INTERSECT", "INVARIANT", "LE", 
		"LENGTH", "LISTEX", "LIT", "LT", "METHOD", "MINUS", "NOT", "OR", "PLUS", 
		"REQUIRES", "RESULTS", "RETURNS", "SET", "SETEX", "THEN", "TIMES", "UNION", 
		"VAR", "WHILE", "WS", "'('", "')'", "','", "':'", "';'", "'['", "']'"
	};
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
	// Pseudo.g:103:1: program : ( method )+ ;
	public final PseudoParser.program_return program() throws RecognitionException {
		PseudoParser.program_return retval = new PseudoParser.program_return();
		retval.start = input.LT(1);

		PseudoTree root_0 = null;

		ParserRuleReturnScope method1 =null;


		try {
			// Pseudo.g:103:8: ( ( method )+ )
			// Pseudo.g:104:3: ( method )+
			{
			root_0 = (PseudoTree)adaptor.nil();


			// Pseudo.g:104:3: ( method )+
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
					// Pseudo.g:104:3: method
					{
					pushFollow(FOLLOW_method_in_program415);
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
	// Pseudo.g:107:1: method : 'method' ID '(' ( vars )? ')' ( returns_ )? ( requires )* ( ensures )* ( decreases )? '{' ( decl )* ( statements )? '}' -> ^( 'method' ID ^( ARGS ( vars )? ) ( returns_ )? ( requires )* ( ensures )* ( decreases )? ( decl )* ^( BLOCK ( statements )? ) ) ;
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
		RewriteRuleTokenStream stream_ID=new RewriteRuleTokenStream(adaptor,"token ID");
		RewriteRuleTokenStream stream_51=new RewriteRuleTokenStream(adaptor,"token 51");
		RewriteRuleTokenStream stream_52=new RewriteRuleTokenStream(adaptor,"token 52");
		RewriteRuleTokenStream stream_BLOCK_BEGIN=new RewriteRuleTokenStream(adaptor,"token BLOCK_BEGIN");
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
			// Pseudo.g:107:7: ( 'method' ID '(' ( vars )? ')' ( returns_ )? ( requires )* ( ensures )* ( decreases )? '{' ( decl )* ( statements )? '}' -> ^( 'method' ID ^( ARGS ( vars )? ) ( returns_ )? ( requires )* ( ensures )* ( decreases )? ( decl )* ^( BLOCK ( statements )? ) ) )
			// Pseudo.g:108:3: 'method' ID '(' ( vars )? ')' ( returns_ )? ( requires )* ( ensures )* ( decreases )? '{' ( decl )* ( statements )? '}'
			{
			string_literal2=(Token)match(input,METHOD,FOLLOW_METHOD_in_method429); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_METHOD.add(string_literal2);

			ID3=(Token)match(input,ID,FOLLOW_ID_in_method431); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_ID.add(ID3);

			char_literal4=(Token)match(input,51,FOLLOW_51_in_method433); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_51.add(char_literal4);

			// Pseudo.g:108:19: ( vars )?
			int alt2=2;
			int LA2_0 = input.LA(1);
			if ( (LA2_0==ID) ) {
				alt2=1;
			}
			switch (alt2) {
				case 1 :
					// Pseudo.g:108:19: vars
					{
					pushFollow(FOLLOW_vars_in_method435);
					vars5=vars();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_vars.add(vars5.getTree());
					}
					break;

			}

			char_literal6=(Token)match(input,52,FOLLOW_52_in_method438); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_52.add(char_literal6);

			// Pseudo.g:109:3: ( returns_ )?
			int alt3=2;
			int LA3_0 = input.LA(1);
			if ( (LA3_0==RETURNS) ) {
				alt3=1;
			}
			switch (alt3) {
				case 1 :
					// Pseudo.g:109:5: returns_
					{
					pushFollow(FOLLOW_returns__in_method444);
					returns_7=returns_();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_returns_.add(returns_7.getTree());
					}
					break;

			}

			// Pseudo.g:110:3: ( requires )*
			loop4:
			while (true) {
				int alt4=2;
				int LA4_0 = input.LA(1);
				if ( (LA4_0==REQUIRES) ) {
					alt4=1;
				}

				switch (alt4) {
				case 1 :
					// Pseudo.g:110:5: requires
					{
					pushFollow(FOLLOW_requires_in_method453);
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

			// Pseudo.g:111:3: ( ensures )*
			loop5:
			while (true) {
				int alt5=2;
				int LA5_0 = input.LA(1);
				if ( (LA5_0==ENSURES) ) {
					alt5=1;
				}

				switch (alt5) {
				case 1 :
					// Pseudo.g:111:5: ensures
					{
					pushFollow(FOLLOW_ensures_in_method462);
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

			// Pseudo.g:112:3: ( decreases )?
			int alt6=2;
			int LA6_0 = input.LA(1);
			if ( (LA6_0==DECREASES) ) {
				alt6=1;
			}
			switch (alt6) {
				case 1 :
					// Pseudo.g:112:5: decreases
					{
					pushFollow(FOLLOW_decreases_in_method471);
					decreases10=decreases();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_decreases.add(decreases10.getTree());
					}
					break;

			}

			char_literal11=(Token)match(input,BLOCK_BEGIN,FOLLOW_BLOCK_BEGIN_in_method478); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_BLOCK_BEGIN.add(char_literal11);

			// Pseudo.g:113:7: ( decl )*
			loop7:
			while (true) {
				int alt7=2;
				int LA7_0 = input.LA(1);
				if ( (LA7_0==VAR) ) {
					alt7=1;
				}

				switch (alt7) {
				case 1 :
					// Pseudo.g:113:9: decl
					{
					pushFollow(FOLLOW_decl_in_method482);
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

			// Pseudo.g:113:17: ( statements )?
			int alt8=2;
			int LA8_0 = input.LA(1);
			if ( (LA8_0==ASSERT||(LA8_0 >= ID && LA8_0 <= IF)||LA8_0==WHILE) ) {
				alt8=1;
			}
			switch (alt8) {
				case 1 :
					// Pseudo.g:113:17: statements
					{
					pushFollow(FOLLOW_statements_in_method487);
					statements13=statements();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_statements.add(statements13.getTree());
					}
					break;

			}

			char_literal14=(Token)match(input,BLOCK_END,FOLLOW_BLOCK_END_in_method490); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_BLOCK_END.add(char_literal14);

			// AST REWRITE
			// elements: returns_, vars, requires, METHOD, decreases, decl, ensures, statements, ID
			// token labels: 
			// rule labels: retval
			// token list labels: 
			// rule list labels: 
			// wildcard labels: 
			if ( state.backtracking==0 ) {
			retval.tree = root_0;
			RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

			root_0 = (PseudoTree)adaptor.nil();
			// 114:3: -> ^( 'method' ID ^( ARGS ( vars )? ) ( returns_ )? ( requires )* ( ensures )* ( decreases )? ( decl )* ^( BLOCK ( statements )? ) )
			{
				// Pseudo.g:115:5: ^( 'method' ID ^( ARGS ( vars )? ) ( returns_ )? ( requires )* ( ensures )* ( decreases )? ( decl )* ^( BLOCK ( statements )? ) )
				{
				PseudoTree root_1 = (PseudoTree)adaptor.nil();
				root_1 = (PseudoTree)adaptor.becomeRoot(stream_METHOD.nextNode(), root_1);
				adaptor.addChild(root_1, stream_ID.nextNode());
				// Pseudo.g:115:19: ^( ARGS ( vars )? )
				{
				PseudoTree root_2 = (PseudoTree)adaptor.nil();
				root_2 = (PseudoTree)adaptor.becomeRoot((PseudoTree)adaptor.create(ARGS, "ARGS"), root_2);
				// Pseudo.g:115:26: ( vars )?
				if ( stream_vars.hasNext() ) {
					adaptor.addChild(root_2, stream_vars.nextTree());
				}
				stream_vars.reset();

				adaptor.addChild(root_1, root_2);
				}

				// Pseudo.g:115:33: ( returns_ )?
				if ( stream_returns_.hasNext() ) {
					adaptor.addChild(root_1, stream_returns_.nextTree());
				}
				stream_returns_.reset();

				// Pseudo.g:115:43: ( requires )*
				while ( stream_requires.hasNext() ) {
					adaptor.addChild(root_1, stream_requires.nextTree());
				}
				stream_requires.reset();

				// Pseudo.g:115:53: ( ensures )*
				while ( stream_ensures.hasNext() ) {
					adaptor.addChild(root_1, stream_ensures.nextTree());
				}
				stream_ensures.reset();

				// Pseudo.g:116:9: ( decreases )?
				if ( stream_decreases.hasNext() ) {
					adaptor.addChild(root_1, stream_decreases.nextTree());
				}
				stream_decreases.reset();

				// Pseudo.g:116:20: ( decl )*
				while ( stream_decl.hasNext() ) {
					adaptor.addChild(root_1, stream_decl.nextTree());
				}
				stream_decl.reset();

				// Pseudo.g:116:26: ^( BLOCK ( statements )? )
				{
				PseudoTree root_2 = (PseudoTree)adaptor.nil();
				root_2 = (PseudoTree)adaptor.becomeRoot((PseudoTree)adaptor.create(BLOCK, "BLOCK"), root_2);
				// Pseudo.g:116:34: ( statements )?
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
	// Pseudo.g:119:1: decl : VAR ! var ';' !;
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
			// Pseudo.g:119:5: ( VAR ! var ';' !)
			// Pseudo.g:120:3: VAR ! var ';' !
			{
			root_0 = (PseudoTree)adaptor.nil();


			VAR15=(Token)match(input,VAR,FOLLOW_VAR_in_decl554); if (state.failed) return retval;
			pushFollow(FOLLOW_var_in_decl557);
			var16=var();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, var16.getTree());

			char_literal17=(Token)match(input,55,FOLLOW_55_in_decl559); if (state.failed) return retval;
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
	// Pseudo.g:123:1: vars : var ( ',' ! var )* ;
	public final PseudoParser.vars_return vars() throws RecognitionException {
		PseudoParser.vars_return retval = new PseudoParser.vars_return();
		retval.start = input.LT(1);

		PseudoTree root_0 = null;

		Token char_literal19=null;
		ParserRuleReturnScope var18 =null;
		ParserRuleReturnScope var20 =null;

		PseudoTree char_literal19_tree=null;

		try {
			// Pseudo.g:123:5: ( var ( ',' ! var )* )
			// Pseudo.g:124:3: var ( ',' ! var )*
			{
			root_0 = (PseudoTree)adaptor.nil();


			pushFollow(FOLLOW_var_in_vars572);
			var18=var();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, var18.getTree());

			// Pseudo.g:125:3: ( ',' ! var )*
			loop9:
			while (true) {
				int alt9=2;
				int LA9_0 = input.LA(1);
				if ( (LA9_0==53) ) {
					alt9=1;
				}

				switch (alt9) {
				case 1 :
					// Pseudo.g:125:5: ',' ! var
					{
					char_literal19=(Token)match(input,53,FOLLOW_53_in_vars578); if (state.failed) return retval;
					pushFollow(FOLLOW_var_in_vars581);
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
	// Pseudo.g:128:1: var : ID ':' type -> ^( VAR ID type ) ;
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
		RewriteRuleTokenStream stream_54=new RewriteRuleTokenStream(adaptor,"token 54");
		RewriteRuleSubtreeStream stream_type=new RewriteRuleSubtreeStream(adaptor,"rule type");

		try {
			// Pseudo.g:128:4: ( ID ':' type -> ^( VAR ID type ) )
			// Pseudo.g:129:3: ID ':' type
			{
			ID21=(Token)match(input,ID,FOLLOW_ID_in_var596); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_ID.add(ID21);

			char_literal22=(Token)match(input,54,FOLLOW_54_in_var598); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_54.add(char_literal22);

			pushFollow(FOLLOW_type_in_var600);
			type23=type();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) stream_type.add(type23.getTree());
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
			// 129:15: -> ^( VAR ID type )
			{
				// Pseudo.g:129:18: ^( VAR ID type )
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
	// Pseudo.g:132:1: type : ( INT | SET ^ '<' ! INT '>' !| ARRAY ^ '<' ! INT '>' !);
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
			// Pseudo.g:132:5: ( INT | SET ^ '<' ! INT '>' !| ARRAY ^ '<' ! INT '>' !)
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
					// Pseudo.g:133:5: INT
					{
					root_0 = (PseudoTree)adaptor.nil();


					INT24=(Token)match(input,INT,FOLLOW_INT_in_type624); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					INT24_tree = (PseudoTree)adaptor.create(INT24);
					adaptor.addChild(root_0, INT24_tree);
					}

					}
					break;
				case 2 :
					// Pseudo.g:133:11: SET ^ '<' ! INT '>' !
					{
					root_0 = (PseudoTree)adaptor.nil();


					SET25=(Token)match(input,SET,FOLLOW_SET_in_type628); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					SET25_tree = (PseudoTree)adaptor.create(SET25);
					root_0 = (PseudoTree)adaptor.becomeRoot(SET25_tree, root_0);
					}

					char_literal26=(Token)match(input,LT,FOLLOW_LT_in_type631); if (state.failed) return retval;
					INT27=(Token)match(input,INT,FOLLOW_INT_in_type634); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					INT27_tree = (PseudoTree)adaptor.create(INT27);
					adaptor.addChild(root_0, INT27_tree);
					}

					char_literal28=(Token)match(input,GT,FOLLOW_GT_in_type636); if (state.failed) return retval;
					}
					break;
				case 3 :
					// Pseudo.g:134:5: ARRAY ^ '<' ! INT '>' !
					{
					root_0 = (PseudoTree)adaptor.nil();


					ARRAY29=(Token)match(input,ARRAY,FOLLOW_ARRAY_in_type643); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					ARRAY29_tree = (PseudoTree)adaptor.create(ARRAY29);
					root_0 = (PseudoTree)adaptor.becomeRoot(ARRAY29_tree, root_0);
					}

					char_literal30=(Token)match(input,LT,FOLLOW_LT_in_type646); if (state.failed) return retval;
					INT31=(Token)match(input,INT,FOLLOW_INT_in_type649); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					INT31_tree = (PseudoTree)adaptor.create(INT31);
					adaptor.addChild(root_0, INT31_tree);
					}

					char_literal32=(Token)match(input,GT,FOLLOW_GT_in_type651); if (state.failed) return retval;
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
	// Pseudo.g:137:1: returns_ : RETURNS ^ '(' ! vars ')' !;
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
			// Pseudo.g:137:9: ( RETURNS ^ '(' ! vars ')' !)
			// Pseudo.g:138:3: RETURNS ^ '(' ! vars ')' !
			{
			root_0 = (PseudoTree)adaptor.nil();


			RETURNS33=(Token)match(input,RETURNS,FOLLOW_RETURNS_in_returns_664); if (state.failed) return retval;
			if ( state.backtracking==0 ) {
			RETURNS33_tree = (PseudoTree)adaptor.create(RETURNS33);
			root_0 = (PseudoTree)adaptor.becomeRoot(RETURNS33_tree, root_0);
			}

			char_literal34=(Token)match(input,51,FOLLOW_51_in_returns_667); if (state.failed) return retval;
			pushFollow(FOLLOW_vars_in_returns_670);
			vars35=vars();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, vars35.getTree());

			char_literal36=(Token)match(input,52,FOLLOW_52_in_returns_672); if (state.failed) return retval;
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
	// Pseudo.g:141:1: requires : REQUIRES ^ ( ID ':' !)? expression ;
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
			// Pseudo.g:141:9: ( REQUIRES ^ ( ID ':' !)? expression )
			// Pseudo.g:142:3: REQUIRES ^ ( ID ':' !)? expression
			{
			root_0 = (PseudoTree)adaptor.nil();


			REQUIRES37=(Token)match(input,REQUIRES,FOLLOW_REQUIRES_in_requires685); if (state.failed) return retval;
			if ( state.backtracking==0 ) {
			REQUIRES37_tree = (PseudoTree)adaptor.create(REQUIRES37);
			root_0 = (PseudoTree)adaptor.becomeRoot(REQUIRES37_tree, root_0);
			}

			// Pseudo.g:142:13: ( ID ':' !)?
			int alt11=2;
			int LA11_0 = input.LA(1);
			if ( (LA11_0==ID) ) {
				int LA11_1 = input.LA(2);
				if ( (LA11_1==54) ) {
					alt11=1;
				}
			}
			switch (alt11) {
				case 1 :
					// Pseudo.g:142:14: ID ':' !
					{
					ID38=(Token)match(input,ID,FOLLOW_ID_in_requires689); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					ID38_tree = (PseudoTree)adaptor.create(ID38);
					adaptor.addChild(root_0, ID38_tree);
					}

					char_literal39=(Token)match(input,54,FOLLOW_54_in_requires691); if (state.failed) return retval;
					}
					break;

			}

			pushFollow(FOLLOW_expression_in_requires696);
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
	// Pseudo.g:145:1: ensures : ENSURES ^ ( ID ':' !)? expression ;
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
			// Pseudo.g:145:8: ( ENSURES ^ ( ID ':' !)? expression )
			// Pseudo.g:146:3: ENSURES ^ ( ID ':' !)? expression
			{
			root_0 = (PseudoTree)adaptor.nil();


			ENSURES41=(Token)match(input,ENSURES,FOLLOW_ENSURES_in_ensures708); if (state.failed) return retval;
			if ( state.backtracking==0 ) {
			ENSURES41_tree = (PseudoTree)adaptor.create(ENSURES41);
			root_0 = (PseudoTree)adaptor.becomeRoot(ENSURES41_tree, root_0);
			}

			// Pseudo.g:146:12: ( ID ':' !)?
			int alt12=2;
			int LA12_0 = input.LA(1);
			if ( (LA12_0==ID) ) {
				int LA12_1 = input.LA(2);
				if ( (LA12_1==54) ) {
					alt12=1;
				}
			}
			switch (alt12) {
				case 1 :
					// Pseudo.g:146:13: ID ':' !
					{
					ID42=(Token)match(input,ID,FOLLOW_ID_in_ensures712); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					ID42_tree = (PseudoTree)adaptor.create(ID42);
					adaptor.addChild(root_0, ID42_tree);
					}

					char_literal43=(Token)match(input,54,FOLLOW_54_in_ensures714); if (state.failed) return retval;
					}
					break;

			}

			pushFollow(FOLLOW_expression_in_ensures719);
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
	// Pseudo.g:149:1: decreases : DECREASES ^ expression ;
	public final PseudoParser.decreases_return decreases() throws RecognitionException {
		PseudoParser.decreases_return retval = new PseudoParser.decreases_return();
		retval.start = input.LT(1);

		PseudoTree root_0 = null;

		Token DECREASES45=null;
		ParserRuleReturnScope expression46 =null;

		PseudoTree DECREASES45_tree=null;

		try {
			// Pseudo.g:149:10: ( DECREASES ^ expression )
			// Pseudo.g:150:3: DECREASES ^ expression
			{
			root_0 = (PseudoTree)adaptor.nil();


			DECREASES45=(Token)match(input,DECREASES,FOLLOW_DECREASES_in_decreases731); if (state.failed) return retval;
			if ( state.backtracking==0 ) {
			DECREASES45_tree = (PseudoTree)adaptor.create(DECREASES45);
			root_0 = (PseudoTree)adaptor.becomeRoot(DECREASES45_tree, root_0);
			}

			pushFollow(FOLLOW_expression_in_decreases734);
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
	// Pseudo.g:153:1: invariant : INVARIANT ^ ( ID ':' !)? expression ;
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
			// Pseudo.g:153:10: ( INVARIANT ^ ( ID ':' !)? expression )
			// Pseudo.g:154:3: INVARIANT ^ ( ID ':' !)? expression
			{
			root_0 = (PseudoTree)adaptor.nil();


			INVARIANT47=(Token)match(input,INVARIANT,FOLLOW_INVARIANT_in_invariant746); if (state.failed) return retval;
			if ( state.backtracking==0 ) {
			INVARIANT47_tree = (PseudoTree)adaptor.create(INVARIANT47);
			root_0 = (PseudoTree)adaptor.becomeRoot(INVARIANT47_tree, root_0);
			}

			// Pseudo.g:154:14: ( ID ':' !)?
			int alt13=2;
			int LA13_0 = input.LA(1);
			if ( (LA13_0==ID) ) {
				int LA13_1 = input.LA(2);
				if ( (LA13_1==54) ) {
					alt13=1;
				}
			}
			switch (alt13) {
				case 1 :
					// Pseudo.g:154:15: ID ':' !
					{
					ID48=(Token)match(input,ID,FOLLOW_ID_in_invariant750); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					ID48_tree = (PseudoTree)adaptor.create(ID48);
					adaptor.addChild(root_0, ID48_tree);
					}

					char_literal49=(Token)match(input,54,FOLLOW_54_in_invariant752); if (state.failed) return retval;
					}
					break;

			}

			pushFollow(FOLLOW_expression_in_invariant757);
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
	// Pseudo.g:157:1: block : '{' ( statements )? '}' -> ^( BLOCK ( statements )? ) ;
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
			// Pseudo.g:157:6: ( '{' ( statements )? '}' -> ^( BLOCK ( statements )? ) )
			// Pseudo.g:158:3: '{' ( statements )? '}'
			{
			char_literal51=(Token)match(input,BLOCK_BEGIN,FOLLOW_BLOCK_BEGIN_in_block769); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_BLOCK_BEGIN.add(char_literal51);

			// Pseudo.g:158:7: ( statements )?
			int alt14=2;
			int LA14_0 = input.LA(1);
			if ( (LA14_0==ASSERT||(LA14_0 >= ID && LA14_0 <= IF)||LA14_0==WHILE) ) {
				alt14=1;
			}
			switch (alt14) {
				case 1 :
					// Pseudo.g:158:7: statements
					{
					pushFollow(FOLLOW_statements_in_block771);
					statements52=statements();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_statements.add(statements52.getTree());
					}
					break;

			}

			char_literal53=(Token)match(input,BLOCK_END,FOLLOW_BLOCK_END_in_block774); if (state.failed) return retval; 
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
			// 158:23: -> ^( BLOCK ( statements )? )
			{
				// Pseudo.g:158:26: ^( BLOCK ( statements )? )
				{
				PseudoTree root_1 = (PseudoTree)adaptor.nil();
				root_1 = (PseudoTree)adaptor.becomeRoot((PseudoTree)adaptor.create(BLOCK, "BLOCK"), root_1);
				// Pseudo.g:158:34: ( statements )?
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
	// Pseudo.g:161:1: relaxedBlock : ( block | statement -> ^( BLOCK statement ) );
	public final PseudoParser.relaxedBlock_return relaxedBlock() throws RecognitionException {
		PseudoParser.relaxedBlock_return retval = new PseudoParser.relaxedBlock_return();
		retval.start = input.LT(1);

		PseudoTree root_0 = null;

		ParserRuleReturnScope block54 =null;
		ParserRuleReturnScope statement55 =null;

		RewriteRuleSubtreeStream stream_statement=new RewriteRuleSubtreeStream(adaptor,"rule statement");

		try {
			// Pseudo.g:161:13: ( block | statement -> ^( BLOCK statement ) )
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
					// Pseudo.g:162:5: block
					{
					root_0 = (PseudoTree)adaptor.nil();


					pushFollow(FOLLOW_block_in_relaxedBlock797);
					block54=block();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, block54.getTree());

					}
					break;
				case 2 :
					// Pseudo.g:163:5: statement
					{
					pushFollow(FOLLOW_statement_in_relaxedBlock803);
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
					// 163:15: -> ^( BLOCK statement )
					{
						// Pseudo.g:163:18: ^( BLOCK statement )
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
	// Pseudo.g:166:1: statements : ( statement )+ ;
	public final PseudoParser.statements_return statements() throws RecognitionException {
		PseudoParser.statements_return retval = new PseudoParser.statements_return();
		retval.start = input.LT(1);

		PseudoTree root_0 = null;

		ParserRuleReturnScope statement56 =null;


		try {
			// Pseudo.g:166:11: ( ( statement )+ )
			// Pseudo.g:167:3: ( statement )+
			{
			root_0 = (PseudoTree)adaptor.nil();


			// Pseudo.g:167:3: ( statement )+
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
					// Pseudo.g:167:5: statement
					{
					pushFollow(FOLLOW_statement_in_statements825);
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
	// Pseudo.g:170:1: statement : ( ID ':=' ^ expression ';' !| ( ID ':=' 'call' )=>r= ID ':=' 'call' f= ID '(' ( expressions )? ')' ';' -> ^( 'call' $f ^( RESULTS $r) ^( ARGS ( expressions )? ) ) | ids ':=' 'call' ID '(' ( expressions )? ')' ';' -> ^( 'call' ID ^( RESULTS ids ) ^( ARGS ( expressions )? ) ) | 'while' ^ expression ( invariant )+ decreases relaxedBlock | 'if' ^ expression relaxedBlock ( options {greedy=true; } : 'else' ! relaxedBlock )? | 'assert' ^ ( ID ':' !)? expression ';' !);
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
		RewriteRuleTokenStream stream_CALL=new RewriteRuleTokenStream(adaptor,"token CALL");
		RewriteRuleTokenStream stream_55=new RewriteRuleTokenStream(adaptor,"token 55");
		RewriteRuleTokenStream stream_ID=new RewriteRuleTokenStream(adaptor,"token ID");
		RewriteRuleTokenStream stream_51=new RewriteRuleTokenStream(adaptor,"token 51");
		RewriteRuleTokenStream stream_52=new RewriteRuleTokenStream(adaptor,"token 52");
		RewriteRuleTokenStream stream_ASSIGN=new RewriteRuleTokenStream(adaptor,"token ASSIGN");
		RewriteRuleSubtreeStream stream_ids=new RewriteRuleSubtreeStream(adaptor,"rule ids");
		RewriteRuleSubtreeStream stream_expressions=new RewriteRuleSubtreeStream(adaptor,"rule expressions");

		try {
			// Pseudo.g:170:10: ( ID ':=' ^ expression ';' !| ( ID ':=' 'call' )=>r= ID ':=' 'call' f= ID '(' ( expressions )? ')' ';' -> ^( 'call' $f ^( RESULTS $r) ^( ARGS ( expressions )? ) ) | ids ':=' 'call' ID '(' ( expressions )? ')' ';' -> ^( 'call' ID ^( RESULTS ids ) ^( ARGS ( expressions )? ) ) | 'while' ^ expression ( invariant )+ decreases relaxedBlock | 'if' ^ expression relaxedBlock ( options {greedy=true; } : 'else' ! relaxedBlock )? | 'assert' ^ ( ID ':' !)? expression ';' !)
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
					else if ( (LA22_5==BLOCK_BEGIN||LA22_5==ID||LA22_5==LIT||(LA22_5 >= MINUS && LA22_5 <= NOT)||LA22_5==51||LA22_5==56) ) {
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
				else if ( (LA22_1==53) ) {
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
					// Pseudo.g:171:5: ID ':=' ^ expression ';' !
					{
					root_0 = (PseudoTree)adaptor.nil();


					ID57=(Token)match(input,ID,FOLLOW_ID_in_statement842); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					ID57_tree = (PseudoTree)adaptor.create(ID57);
					adaptor.addChild(root_0, ID57_tree);
					}

					string_literal58=(Token)match(input,ASSIGN,FOLLOW_ASSIGN_in_statement844); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					string_literal58_tree = (PseudoTree)adaptor.create(string_literal58);
					root_0 = (PseudoTree)adaptor.becomeRoot(string_literal58_tree, root_0);
					}

					pushFollow(FOLLOW_expression_in_statement847);
					expression59=expression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, expression59.getTree());

					char_literal60=(Token)match(input,55,FOLLOW_55_in_statement849); if (state.failed) return retval;
					}
					break;
				case 2 :
					// Pseudo.g:172:5: ( ID ':=' 'call' )=>r= ID ':=' 'call' f= ID '(' ( expressions )? ')' ';'
					{
					r=(Token)match(input,ID,FOLLOW_ID_in_statement868); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_ID.add(r);

					string_literal61=(Token)match(input,ASSIGN,FOLLOW_ASSIGN_in_statement870); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_ASSIGN.add(string_literal61);

					string_literal62=(Token)match(input,CALL,FOLLOW_CALL_in_statement872); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_CALL.add(string_literal62);

					f=(Token)match(input,ID,FOLLOW_ID_in_statement876); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_ID.add(f);

					char_literal63=(Token)match(input,51,FOLLOW_51_in_statement878); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_51.add(char_literal63);

					// Pseudo.g:172:51: ( expressions )?
					int alt17=2;
					int LA17_0 = input.LA(1);
					if ( (LA17_0==BLOCK_BEGIN||LA17_0==ID||LA17_0==LIT||(LA17_0 >= MINUS && LA17_0 <= NOT)||LA17_0==51||LA17_0==56) ) {
						alt17=1;
					}
					switch (alt17) {
						case 1 :
							// Pseudo.g:172:51: expressions
							{
							pushFollow(FOLLOW_expressions_in_statement880);
							expressions64=expressions();
							state._fsp--;
							if (state.failed) return retval;
							if ( state.backtracking==0 ) stream_expressions.add(expressions64.getTree());
							}
							break;

					}

					char_literal65=(Token)match(input,52,FOLLOW_52_in_statement883); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_52.add(char_literal65);

					char_literal66=(Token)match(input,55,FOLLOW_55_in_statement885); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_55.add(char_literal66);

					// AST REWRITE
					// elements: f, expressions, r, CALL
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
					// 173:9: -> ^( 'call' $f ^( RESULTS $r) ^( ARGS ( expressions )? ) )
					{
						// Pseudo.g:173:12: ^( 'call' $f ^( RESULTS $r) ^( ARGS ( expressions )? ) )
						{
						PseudoTree root_1 = (PseudoTree)adaptor.nil();
						root_1 = (PseudoTree)adaptor.becomeRoot(stream_CALL.nextNode(), root_1);
						adaptor.addChild(root_1, stream_f.nextNode());
						// Pseudo.g:173:24: ^( RESULTS $r)
						{
						PseudoTree root_2 = (PseudoTree)adaptor.nil();
						root_2 = (PseudoTree)adaptor.becomeRoot((PseudoTree)adaptor.create(RESULTS, "RESULTS"), root_2);
						adaptor.addChild(root_2, stream_r.nextNode());
						adaptor.addChild(root_1, root_2);
						}

						// Pseudo.g:173:38: ^( ARGS ( expressions )? )
						{
						PseudoTree root_2 = (PseudoTree)adaptor.nil();
						root_2 = (PseudoTree)adaptor.becomeRoot((PseudoTree)adaptor.create(ARGS, "ARGS"), root_2);
						// Pseudo.g:173:45: ( expressions )?
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
					// Pseudo.g:174:5: ids ':=' 'call' ID '(' ( expressions )? ')' ';'
					{
					pushFollow(FOLLOW_ids_in_statement922);
					ids67=ids();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_ids.add(ids67.getTree());
					string_literal68=(Token)match(input,ASSIGN,FOLLOW_ASSIGN_in_statement924); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_ASSIGN.add(string_literal68);

					string_literal69=(Token)match(input,CALL,FOLLOW_CALL_in_statement926); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_CALL.add(string_literal69);

					ID70=(Token)match(input,ID,FOLLOW_ID_in_statement928); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_ID.add(ID70);

					char_literal71=(Token)match(input,51,FOLLOW_51_in_statement930); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_51.add(char_literal71);

					// Pseudo.g:174:28: ( expressions )?
					int alt18=2;
					int LA18_0 = input.LA(1);
					if ( (LA18_0==BLOCK_BEGIN||LA18_0==ID||LA18_0==LIT||(LA18_0 >= MINUS && LA18_0 <= NOT)||LA18_0==51||LA18_0==56) ) {
						alt18=1;
					}
					switch (alt18) {
						case 1 :
							// Pseudo.g:174:28: expressions
							{
							pushFollow(FOLLOW_expressions_in_statement932);
							expressions72=expressions();
							state._fsp--;
							if (state.failed) return retval;
							if ( state.backtracking==0 ) stream_expressions.add(expressions72.getTree());
							}
							break;

					}

					char_literal73=(Token)match(input,52,FOLLOW_52_in_statement935); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_52.add(char_literal73);

					char_literal74=(Token)match(input,55,FOLLOW_55_in_statement937); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_55.add(char_literal74);

					// AST REWRITE
					// elements: ids, CALL, ID, expressions
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (PseudoTree)adaptor.nil();
					// 175:9: -> ^( 'call' ID ^( RESULTS ids ) ^( ARGS ( expressions )? ) )
					{
						// Pseudo.g:175:12: ^( 'call' ID ^( RESULTS ids ) ^( ARGS ( expressions )? ) )
						{
						PseudoTree root_1 = (PseudoTree)adaptor.nil();
						root_1 = (PseudoTree)adaptor.becomeRoot(stream_CALL.nextNode(), root_1);
						adaptor.addChild(root_1, stream_ID.nextNode());
						// Pseudo.g:175:24: ^( RESULTS ids )
						{
						PseudoTree root_2 = (PseudoTree)adaptor.nil();
						root_2 = (PseudoTree)adaptor.becomeRoot((PseudoTree)adaptor.create(RESULTS, "RESULTS"), root_2);
						adaptor.addChild(root_2, stream_ids.nextTree());
						adaptor.addChild(root_1, root_2);
						}

						// Pseudo.g:175:39: ^( ARGS ( expressions )? )
						{
						PseudoTree root_2 = (PseudoTree)adaptor.nil();
						root_2 = (PseudoTree)adaptor.becomeRoot((PseudoTree)adaptor.create(ARGS, "ARGS"), root_2);
						// Pseudo.g:175:46: ( expressions )?
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
					// Pseudo.g:176:5: 'while' ^ expression ( invariant )+ decreases relaxedBlock
					{
					root_0 = (PseudoTree)adaptor.nil();


					string_literal75=(Token)match(input,WHILE,FOLLOW_WHILE_in_statement972); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					string_literal75_tree = (PseudoTree)adaptor.create(string_literal75);
					root_0 = (PseudoTree)adaptor.becomeRoot(string_literal75_tree, root_0);
					}

					pushFollow(FOLLOW_expression_in_statement975);
					expression76=expression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, expression76.getTree());

					// Pseudo.g:177:7: ( invariant )+
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
							// Pseudo.g:177:7: invariant
							{
							pushFollow(FOLLOW_invariant_in_statement983);
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

					pushFollow(FOLLOW_decreases_in_statement992);
					decreases78=decreases();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, decreases78.getTree());

					pushFollow(FOLLOW_relaxedBlock_in_statement1000);
					relaxedBlock79=relaxedBlock();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, relaxedBlock79.getTree());

					}
					break;
				case 5 :
					// Pseudo.g:180:5: 'if' ^ expression relaxedBlock ( options {greedy=true; } : 'else' ! relaxedBlock )?
					{
					root_0 = (PseudoTree)adaptor.nil();


					string_literal80=(Token)match(input,IF,FOLLOW_IF_in_statement1006); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					string_literal80_tree = (PseudoTree)adaptor.create(string_literal80);
					root_0 = (PseudoTree)adaptor.becomeRoot(string_literal80_tree, root_0);
					}

					pushFollow(FOLLOW_expression_in_statement1009);
					expression81=expression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, expression81.getTree());

					pushFollow(FOLLOW_relaxedBlock_in_statement1011);
					relaxedBlock82=relaxedBlock();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, relaxedBlock82.getTree());

					// Pseudo.g:181:7: ( options {greedy=true; } : 'else' ! relaxedBlock )?
					int alt20=2;
					int LA20_0 = input.LA(1);
					if ( (LA20_0==ELSE) ) {
						alt20=1;
					}
					switch (alt20) {
						case 1 :
							// Pseudo.g:181:36: 'else' ! relaxedBlock
							{
							string_literal83=(Token)match(input,ELSE,FOLLOW_ELSE_in_statement1032); if (state.failed) return retval;
							pushFollow(FOLLOW_relaxedBlock_in_statement1035);
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
					// Pseudo.g:182:5: 'assert' ^ ( ID ':' !)? expression ';' !
					{
					root_0 = (PseudoTree)adaptor.nil();


					string_literal85=(Token)match(input,ASSERT,FOLLOW_ASSERT_in_statement1044); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					string_literal85_tree = (PseudoTree)adaptor.create(string_literal85);
					root_0 = (PseudoTree)adaptor.becomeRoot(string_literal85_tree, root_0);
					}

					// Pseudo.g:182:15: ( ID ':' !)?
					int alt21=2;
					int LA21_0 = input.LA(1);
					if ( (LA21_0==ID) ) {
						int LA21_1 = input.LA(2);
						if ( (LA21_1==54) ) {
							alt21=1;
						}
					}
					switch (alt21) {
						case 1 :
							// Pseudo.g:182:17: ID ':' !
							{
							ID86=(Token)match(input,ID,FOLLOW_ID_in_statement1049); if (state.failed) return retval;
							if ( state.backtracking==0 ) {
							ID86_tree = (PseudoTree)adaptor.create(ID86);
							adaptor.addChild(root_0, ID86_tree);
							}

							char_literal87=(Token)match(input,54,FOLLOW_54_in_statement1051); if (state.failed) return retval;
							}
							break;

					}

					pushFollow(FOLLOW_expression_in_statement1057);
					expression88=expression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, expression88.getTree());

					char_literal89=(Token)match(input,55,FOLLOW_55_in_statement1059); if (state.failed) return retval;
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
	// Pseudo.g:185:1: ids : ID ( ',' ! ID )+ ;
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
			// Pseudo.g:185:4: ( ID ( ',' ! ID )+ )
			// Pseudo.g:186:3: ID ( ',' ! ID )+
			{
			root_0 = (PseudoTree)adaptor.nil();


			ID90=(Token)match(input,ID,FOLLOW_ID_in_ids1072); if (state.failed) return retval;
			if ( state.backtracking==0 ) {
			ID90_tree = (PseudoTree)adaptor.create(ID90);
			adaptor.addChild(root_0, ID90_tree);
			}

			// Pseudo.g:186:6: ( ',' ! ID )+
			int cnt23=0;
			loop23:
			while (true) {
				int alt23=2;
				int LA23_0 = input.LA(1);
				if ( (LA23_0==53) ) {
					alt23=1;
				}

				switch (alt23) {
				case 1 :
					// Pseudo.g:186:7: ',' ! ID
					{
					char_literal91=(Token)match(input,53,FOLLOW_53_in_ids1075); if (state.failed) return retval;
					ID92=(Token)match(input,ID,FOLLOW_ID_in_ids1078); if (state.failed) return retval;
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
	// Pseudo.g:189:1: expressions : expression ( ',' ! expression )* ;
	public final PseudoParser.expressions_return expressions() throws RecognitionException {
		PseudoParser.expressions_return retval = new PseudoParser.expressions_return();
		retval.start = input.LT(1);

		PseudoTree root_0 = null;

		Token char_literal94=null;
		ParserRuleReturnScope expression93 =null;
		ParserRuleReturnScope expression95 =null;

		PseudoTree char_literal94_tree=null;

		try {
			// Pseudo.g:189:12: ( expression ( ',' ! expression )* )
			// Pseudo.g:190:3: expression ( ',' ! expression )*
			{
			root_0 = (PseudoTree)adaptor.nil();


			pushFollow(FOLLOW_expression_in_expressions1092);
			expression93=expression();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, expression93.getTree());

			// Pseudo.g:190:14: ( ',' ! expression )*
			loop24:
			while (true) {
				int alt24=2;
				int LA24_0 = input.LA(1);
				if ( (LA24_0==53) ) {
					alt24=1;
				}

				switch (alt24) {
				case 1 :
					// Pseudo.g:190:16: ',' ! expression
					{
					char_literal94=(Token)match(input,53,FOLLOW_53_in_expressions1096); if (state.failed) return retval;
					pushFollow(FOLLOW_expression_in_expressions1099);
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
	// Pseudo.g:193:1: expression : or_expr ;
	public final PseudoParser.expression_return expression() throws RecognitionException {
		PseudoParser.expression_return retval = new PseudoParser.expression_return();
		retval.start = input.LT(1);

		PseudoTree root_0 = null;

		ParserRuleReturnScope or_expr96 =null;


		try {
			// Pseudo.g:193:11: ( or_expr )
			// Pseudo.g:194:3: or_expr
			{
			root_0 = (PseudoTree)adaptor.nil();


			pushFollow(FOLLOW_or_expr_in_expression1114);
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
	// Pseudo.g:196:1: or_expr : and_expr ( ( '||' ^| '==>' ^) or_expr )? ;
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
			// Pseudo.g:196:8: ( and_expr ( ( '||' ^| '==>' ^) or_expr )? )
			// Pseudo.g:197:3: and_expr ( ( '||' ^| '==>' ^) or_expr )?
			{
			root_0 = (PseudoTree)adaptor.nil();


			pushFollow(FOLLOW_and_expr_in_or_expr1123);
			and_expr97=and_expr();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, and_expr97.getTree());

			// Pseudo.g:197:12: ( ( '||' ^| '==>' ^) or_expr )?
			int alt26=2;
			int LA26_0 = input.LA(1);
			if ( (LA26_0==IMPLIES||LA26_0==OR) ) {
				alt26=1;
			}
			switch (alt26) {
				case 1 :
					// Pseudo.g:197:14: ( '||' ^| '==>' ^) or_expr
					{
					// Pseudo.g:197:14: ( '||' ^| '==>' ^)
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
							// Pseudo.g:197:15: '||' ^
							{
							string_literal98=(Token)match(input,OR,FOLLOW_OR_in_or_expr1128); if (state.failed) return retval;
							if ( state.backtracking==0 ) {
							string_literal98_tree = (PseudoTree)adaptor.create(string_literal98);
							root_0 = (PseudoTree)adaptor.becomeRoot(string_literal98_tree, root_0);
							}

							}
							break;
						case 2 :
							// Pseudo.g:197:23: '==>' ^
							{
							string_literal99=(Token)match(input,IMPLIES,FOLLOW_IMPLIES_in_or_expr1133); if (state.failed) return retval;
							if ( state.backtracking==0 ) {
							string_literal99_tree = (PseudoTree)adaptor.create(string_literal99);
							root_0 = (PseudoTree)adaptor.becomeRoot(string_literal99_tree, root_0);
							}

							}
							break;

					}

					pushFollow(FOLLOW_or_expr_in_or_expr1137);
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
	// Pseudo.g:200:1: and_expr : rel_expr ( '&&' ^ and_expr )? ;
	public final PseudoParser.and_expr_return and_expr() throws RecognitionException {
		PseudoParser.and_expr_return retval = new PseudoParser.and_expr_return();
		retval.start = input.LT(1);

		PseudoTree root_0 = null;

		Token string_literal102=null;
		ParserRuleReturnScope rel_expr101 =null;
		ParserRuleReturnScope and_expr103 =null;

		PseudoTree string_literal102_tree=null;

		try {
			// Pseudo.g:200:9: ( rel_expr ( '&&' ^ and_expr )? )
			// Pseudo.g:201:3: rel_expr ( '&&' ^ and_expr )?
			{
			root_0 = (PseudoTree)adaptor.nil();


			pushFollow(FOLLOW_rel_expr_in_and_expr1152);
			rel_expr101=rel_expr();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, rel_expr101.getTree());

			// Pseudo.g:201:12: ( '&&' ^ and_expr )?
			int alt27=2;
			int LA27_0 = input.LA(1);
			if ( (LA27_0==AND) ) {
				alt27=1;
			}
			switch (alt27) {
				case 1 :
					// Pseudo.g:201:14: '&&' ^ and_expr
					{
					string_literal102=(Token)match(input,AND,FOLLOW_AND_in_and_expr1156); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					string_literal102_tree = (PseudoTree)adaptor.create(string_literal102);
					root_0 = (PseudoTree)adaptor.becomeRoot(string_literal102_tree, root_0);
					}

					pushFollow(FOLLOW_and_expr_in_and_expr1159);
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
	// Pseudo.g:204:1: rel_expr : add_expr ( ( '<' ^| '>' ^| '==' ^| '<=' ^| '>=' ^) add_expr )? ;
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
			// Pseudo.g:204:9: ( add_expr ( ( '<' ^| '>' ^| '==' ^| '<=' ^| '>=' ^) add_expr )? )
			// Pseudo.g:205:3: add_expr ( ( '<' ^| '>' ^| '==' ^| '<=' ^| '>=' ^) add_expr )?
			{
			root_0 = (PseudoTree)adaptor.nil();


			pushFollow(FOLLOW_add_expr_in_rel_expr1174);
			add_expr104=add_expr();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, add_expr104.getTree());

			// Pseudo.g:205:12: ( ( '<' ^| '>' ^| '==' ^| '<=' ^| '>=' ^) add_expr )?
			int alt29=2;
			int LA29_0 = input.LA(1);
			if ( (LA29_0==EQ||(LA29_0 >= GE && LA29_0 <= GT)||LA29_0==LE||LA29_0==LT) ) {
				alt29=1;
			}
			switch (alt29) {
				case 1 :
					// Pseudo.g:205:14: ( '<' ^| '>' ^| '==' ^| '<=' ^| '>=' ^) add_expr
					{
					// Pseudo.g:205:14: ( '<' ^| '>' ^| '==' ^| '<=' ^| '>=' ^)
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
							// Pseudo.g:205:15: '<' ^
							{
							char_literal105=(Token)match(input,LT,FOLLOW_LT_in_rel_expr1179); if (state.failed) return retval;
							if ( state.backtracking==0 ) {
							char_literal105_tree = (PseudoTree)adaptor.create(char_literal105);
							root_0 = (PseudoTree)adaptor.becomeRoot(char_literal105_tree, root_0);
							}

							}
							break;
						case 2 :
							// Pseudo.g:205:22: '>' ^
							{
							char_literal106=(Token)match(input,GT,FOLLOW_GT_in_rel_expr1184); if (state.failed) return retval;
							if ( state.backtracking==0 ) {
							char_literal106_tree = (PseudoTree)adaptor.create(char_literal106);
							root_0 = (PseudoTree)adaptor.becomeRoot(char_literal106_tree, root_0);
							}

							}
							break;
						case 3 :
							// Pseudo.g:205:29: '==' ^
							{
							string_literal107=(Token)match(input,EQ,FOLLOW_EQ_in_rel_expr1189); if (state.failed) return retval;
							if ( state.backtracking==0 ) {
							string_literal107_tree = (PseudoTree)adaptor.create(string_literal107);
							root_0 = (PseudoTree)adaptor.becomeRoot(string_literal107_tree, root_0);
							}

							}
							break;
						case 4 :
							// Pseudo.g:205:37: '<=' ^
							{
							string_literal108=(Token)match(input,LE,FOLLOW_LE_in_rel_expr1194); if (state.failed) return retval;
							if ( state.backtracking==0 ) {
							string_literal108_tree = (PseudoTree)adaptor.create(string_literal108);
							root_0 = (PseudoTree)adaptor.becomeRoot(string_literal108_tree, root_0);
							}

							}
							break;
						case 5 :
							// Pseudo.g:205:45: '>=' ^
							{
							string_literal109=(Token)match(input,GE,FOLLOW_GE_in_rel_expr1199); if (state.failed) return retval;
							if ( state.backtracking==0 ) {
							string_literal109_tree = (PseudoTree)adaptor.create(string_literal109);
							root_0 = (PseudoTree)adaptor.becomeRoot(string_literal109_tree, root_0);
							}

							}
							break;

					}

					pushFollow(FOLLOW_add_expr_in_rel_expr1203);
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
	// Pseudo.g:208:1: add_expr : mul_expr ( ( '+' | '-' | '++' ) ^ add_expr )? ;
	public final PseudoParser.add_expr_return add_expr() throws RecognitionException {
		PseudoParser.add_expr_return retval = new PseudoParser.add_expr_return();
		retval.start = input.LT(1);

		PseudoTree root_0 = null;

		Token set112=null;
		ParserRuleReturnScope mul_expr111 =null;
		ParserRuleReturnScope add_expr113 =null;

		PseudoTree set112_tree=null;

		try {
			// Pseudo.g:208:9: ( mul_expr ( ( '+' | '-' | '++' ) ^ add_expr )? )
			// Pseudo.g:209:3: mul_expr ( ( '+' | '-' | '++' ) ^ add_expr )?
			{
			root_0 = (PseudoTree)adaptor.nil();


			pushFollow(FOLLOW_mul_expr_in_add_expr1218);
			mul_expr111=mul_expr();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, mul_expr111.getTree());

			// Pseudo.g:209:12: ( ( '+' | '-' | '++' ) ^ add_expr )?
			int alt30=2;
			int LA30_0 = input.LA(1);
			if ( (LA30_0==MINUS||LA30_0==PLUS||LA30_0==UNION) ) {
				alt30=1;
			}
			switch (alt30) {
				case 1 :
					// Pseudo.g:209:14: ( '+' | '-' | '++' ) ^ add_expr
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
					pushFollow(FOLLOW_add_expr_in_add_expr1235);
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
	// Pseudo.g:212:1: mul_expr : prefix_expr ( ( '*' | '**' ) ^ mul_expr )? ;
	public final PseudoParser.mul_expr_return mul_expr() throws RecognitionException {
		PseudoParser.mul_expr_return retval = new PseudoParser.mul_expr_return();
		retval.start = input.LT(1);

		PseudoTree root_0 = null;

		Token set115=null;
		ParserRuleReturnScope prefix_expr114 =null;
		ParserRuleReturnScope mul_expr116 =null;

		PseudoTree set115_tree=null;

		try {
			// Pseudo.g:212:9: ( prefix_expr ( ( '*' | '**' ) ^ mul_expr )? )
			// Pseudo.g:213:3: prefix_expr ( ( '*' | '**' ) ^ mul_expr )?
			{
			root_0 = (PseudoTree)adaptor.nil();


			pushFollow(FOLLOW_prefix_expr_in_mul_expr1250);
			prefix_expr114=prefix_expr();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, prefix_expr114.getTree());

			// Pseudo.g:213:15: ( ( '*' | '**' ) ^ mul_expr )?
			int alt31=2;
			int LA31_0 = input.LA(1);
			if ( (LA31_0==INTERSECT||LA31_0==TIMES) ) {
				alt31=1;
			}
			switch (alt31) {
				case 1 :
					// Pseudo.g:213:17: ( '*' | '**' ) ^ mul_expr
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
					pushFollow(FOLLOW_mul_expr_in_mul_expr1263);
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
	// Pseudo.g:216:1: prefix_expr : ( '-' ^ prefix_expr | '!' ^ prefix_expr | postfix_expr );
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
			// Pseudo.g:216:12: ( '-' ^ prefix_expr | '!' ^ prefix_expr | postfix_expr )
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
			case 51:
			case 56:
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
					// Pseudo.g:217:5: '-' ^ prefix_expr
					{
					root_0 = (PseudoTree)adaptor.nil();


					char_literal117=(Token)match(input,MINUS,FOLLOW_MINUS_in_prefix_expr1280); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					char_literal117_tree = (PseudoTree)adaptor.create(char_literal117);
					root_0 = (PseudoTree)adaptor.becomeRoot(char_literal117_tree, root_0);
					}

					pushFollow(FOLLOW_prefix_expr_in_prefix_expr1283);
					prefix_expr118=prefix_expr();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, prefix_expr118.getTree());

					}
					break;
				case 2 :
					// Pseudo.g:218:5: '!' ^ prefix_expr
					{
					root_0 = (PseudoTree)adaptor.nil();


					char_literal119=(Token)match(input,NOT,FOLLOW_NOT_in_prefix_expr1289); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					char_literal119_tree = (PseudoTree)adaptor.create(char_literal119);
					root_0 = (PseudoTree)adaptor.becomeRoot(char_literal119_tree, root_0);
					}

					pushFollow(FOLLOW_prefix_expr_in_prefix_expr1292);
					prefix_expr120=prefix_expr();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, prefix_expr120.getTree());

					}
					break;
				case 3 :
					// Pseudo.g:219:5: postfix_expr
					{
					root_0 = (PseudoTree)adaptor.nil();


					pushFollow(FOLLOW_postfix_expr_in_prefix_expr1298);
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
	// Pseudo.g:222:1: postfix_expr : atom_expr ( '[' expression ']' -> ^( ARRAY_ACCESS atom_expr expression ) | '.' 'length' -> ^( LENGTH atom_expr ) | -> atom_expr ) ;
	public final PseudoParser.postfix_expr_return postfix_expr() throws RecognitionException {
		PseudoParser.postfix_expr_return retval = new PseudoParser.postfix_expr_return();
		retval.start = input.LT(1);

		PseudoTree root_0 = null;

		Token char_literal123=null;
		Token char_literal125=null;
		Token char_literal126=null;
		Token string_literal127=null;
		ParserRuleReturnScope atom_expr122 =null;
		ParserRuleReturnScope expression124 =null;

		PseudoTree char_literal123_tree=null;
		PseudoTree char_literal125_tree=null;
		PseudoTree char_literal126_tree=null;
		PseudoTree string_literal127_tree=null;
		RewriteRuleTokenStream stream_57=new RewriteRuleTokenStream(adaptor,"token 57");
		RewriteRuleTokenStream stream_56=new RewriteRuleTokenStream(adaptor,"token 56");
		RewriteRuleTokenStream stream_DOT=new RewriteRuleTokenStream(adaptor,"token DOT");
		RewriteRuleTokenStream stream_LENGTH=new RewriteRuleTokenStream(adaptor,"token LENGTH");
		RewriteRuleSubtreeStream stream_expression=new RewriteRuleSubtreeStream(adaptor,"rule expression");
		RewriteRuleSubtreeStream stream_atom_expr=new RewriteRuleSubtreeStream(adaptor,"rule atom_expr");

		try {
			// Pseudo.g:222:13: ( atom_expr ( '[' expression ']' -> ^( ARRAY_ACCESS atom_expr expression ) | '.' 'length' -> ^( LENGTH atom_expr ) | -> atom_expr ) )
			// Pseudo.g:223:3: atom_expr ( '[' expression ']' -> ^( ARRAY_ACCESS atom_expr expression ) | '.' 'length' -> ^( LENGTH atom_expr ) | -> atom_expr )
			{
			pushFollow(FOLLOW_atom_expr_in_postfix_expr1310);
			atom_expr122=atom_expr();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) stream_atom_expr.add(atom_expr122.getTree());
			// Pseudo.g:224:3: ( '[' expression ']' -> ^( ARRAY_ACCESS atom_expr expression ) | '.' 'length' -> ^( LENGTH atom_expr ) | -> atom_expr )
			int alt33=3;
			switch ( input.LA(1) ) {
			case 56:
				{
				alt33=1;
				}
				break;
			case DOT:
				{
				alt33=2;
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
			case LE:
			case LT:
			case MINUS:
			case OR:
			case PLUS:
			case REQUIRES:
			case TIMES:
			case UNION:
			case WHILE:
			case 52:
			case 53:
			case 55:
			case 57:
				{
				alt33=3;
				}
				break;
			default:
				if (state.backtracking>0) {state.failed=true; return retval;}
				NoViableAltException nvae =
					new NoViableAltException("", 33, 0, input);
				throw nvae;
			}
			switch (alt33) {
				case 1 :
					// Pseudo.g:224:5: '[' expression ']'
					{
					char_literal123=(Token)match(input,56,FOLLOW_56_in_postfix_expr1316); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_56.add(char_literal123);

					pushFollow(FOLLOW_expression_in_postfix_expr1318);
					expression124=expression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_expression.add(expression124.getTree());
					char_literal125=(Token)match(input,57,FOLLOW_57_in_postfix_expr1320); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_57.add(char_literal125);

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
					// 224:24: -> ^( ARRAY_ACCESS atom_expr expression )
					{
						// Pseudo.g:224:27: ^( ARRAY_ACCESS atom_expr expression )
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
					// Pseudo.g:225:5: '.' 'length'
					{
					char_literal126=(Token)match(input,DOT,FOLLOW_DOT_in_postfix_expr1338); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_DOT.add(char_literal126);

					string_literal127=(Token)match(input,LENGTH,FOLLOW_LENGTH_in_postfix_expr1340); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_LENGTH.add(string_literal127);

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
					// 225:18: -> ^( LENGTH atom_expr )
					{
						// Pseudo.g:225:21: ^( LENGTH atom_expr )
						{
						PseudoTree root_1 = (PseudoTree)adaptor.nil();
						root_1 = (PseudoTree)adaptor.becomeRoot((PseudoTree)adaptor.create(LENGTH, "LENGTH"), root_1);
						adaptor.addChild(root_1, stream_atom_expr.nextTree());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;
				case 3 :
					// Pseudo.g:226:5: 
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
	// Pseudo.g:230:1: atom_expr : ( ID | LIT | quantifier | '(' ! expression ')' !| '{' ( expressions )? '}' -> ^( SETEX ( expressions )? ) | '[' ( expressions )? ']' -> ^( LISTEX ( expressions )? ) );
	public final PseudoParser.atom_expr_return atom_expr() throws RecognitionException {
		PseudoParser.atom_expr_return retval = new PseudoParser.atom_expr_return();
		retval.start = input.LT(1);

		PseudoTree root_0 = null;

		Token ID128=null;
		Token LIT129=null;
		Token char_literal131=null;
		Token char_literal133=null;
		Token char_literal134=null;
		Token char_literal136=null;
		Token char_literal137=null;
		Token char_literal139=null;
		ParserRuleReturnScope quantifier130 =null;
		ParserRuleReturnScope expression132 =null;
		ParserRuleReturnScope expressions135 =null;
		ParserRuleReturnScope expressions138 =null;

		PseudoTree ID128_tree=null;
		PseudoTree LIT129_tree=null;
		PseudoTree char_literal131_tree=null;
		PseudoTree char_literal133_tree=null;
		PseudoTree char_literal134_tree=null;
		PseudoTree char_literal136_tree=null;
		PseudoTree char_literal137_tree=null;
		PseudoTree char_literal139_tree=null;
		RewriteRuleTokenStream stream_57=new RewriteRuleTokenStream(adaptor,"token 57");
		RewriteRuleTokenStream stream_56=new RewriteRuleTokenStream(adaptor,"token 56");
		RewriteRuleTokenStream stream_BLOCK_BEGIN=new RewriteRuleTokenStream(adaptor,"token BLOCK_BEGIN");
		RewriteRuleTokenStream stream_BLOCK_END=new RewriteRuleTokenStream(adaptor,"token BLOCK_END");
		RewriteRuleSubtreeStream stream_expressions=new RewriteRuleSubtreeStream(adaptor,"rule expressions");

		try {
			// Pseudo.g:230:10: ( ID | LIT | quantifier | '(' ! expression ')' !| '{' ( expressions )? '}' -> ^( SETEX ( expressions )? ) | '[' ( expressions )? ']' -> ^( LISTEX ( expressions )? ) )
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
			case 51:
				{
				int LA36_3 = input.LA(2);
				if ( (LA36_3==ALL||LA36_3==EX) ) {
					alt36=3;
				}
				else if ( (LA36_3==BLOCK_BEGIN||LA36_3==ID||LA36_3==LIT||(LA36_3 >= MINUS && LA36_3 <= NOT)||LA36_3==51||LA36_3==56) ) {
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
			case 56:
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
					// Pseudo.g:231:5: ID
					{
					root_0 = (PseudoTree)adaptor.nil();


					ID128=(Token)match(input,ID,FOLLOW_ID_in_atom_expr1376); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					ID128_tree = (PseudoTree)adaptor.create(ID128);
					adaptor.addChild(root_0, ID128_tree);
					}

					}
					break;
				case 2 :
					// Pseudo.g:232:5: LIT
					{
					root_0 = (PseudoTree)adaptor.nil();


					LIT129=(Token)match(input,LIT,FOLLOW_LIT_in_atom_expr1382); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					LIT129_tree = (PseudoTree)adaptor.create(LIT129);
					adaptor.addChild(root_0, LIT129_tree);
					}

					}
					break;
				case 3 :
					// Pseudo.g:233:5: quantifier
					{
					root_0 = (PseudoTree)adaptor.nil();


					pushFollow(FOLLOW_quantifier_in_atom_expr1388);
					quantifier130=quantifier();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, quantifier130.getTree());

					}
					break;
				case 4 :
					// Pseudo.g:234:5: '(' ! expression ')' !
					{
					root_0 = (PseudoTree)adaptor.nil();


					char_literal131=(Token)match(input,51,FOLLOW_51_in_atom_expr1394); if (state.failed) return retval;
					pushFollow(FOLLOW_expression_in_atom_expr1397);
					expression132=expression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, expression132.getTree());

					char_literal133=(Token)match(input,52,FOLLOW_52_in_atom_expr1399); if (state.failed) return retval;
					}
					break;
				case 5 :
					// Pseudo.g:235:5: '{' ( expressions )? '}'
					{
					char_literal134=(Token)match(input,BLOCK_BEGIN,FOLLOW_BLOCK_BEGIN_in_atom_expr1406); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_BLOCK_BEGIN.add(char_literal134);

					// Pseudo.g:235:9: ( expressions )?
					int alt34=2;
					int LA34_0 = input.LA(1);
					if ( (LA34_0==BLOCK_BEGIN||LA34_0==ID||LA34_0==LIT||(LA34_0 >= MINUS && LA34_0 <= NOT)||LA34_0==51||LA34_0==56) ) {
						alt34=1;
					}
					switch (alt34) {
						case 1 :
							// Pseudo.g:235:9: expressions
							{
							pushFollow(FOLLOW_expressions_in_atom_expr1408);
							expressions135=expressions();
							state._fsp--;
							if (state.failed) return retval;
							if ( state.backtracking==0 ) stream_expressions.add(expressions135.getTree());
							}
							break;

					}

					char_literal136=(Token)match(input,BLOCK_END,FOLLOW_BLOCK_END_in_atom_expr1411); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_BLOCK_END.add(char_literal136);

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
					// 235:26: -> ^( SETEX ( expressions )? )
					{
						// Pseudo.g:235:29: ^( SETEX ( expressions )? )
						{
						PseudoTree root_1 = (PseudoTree)adaptor.nil();
						root_1 = (PseudoTree)adaptor.becomeRoot((PseudoTree)adaptor.create(SETEX, "SETEX"), root_1);
						// Pseudo.g:235:37: ( expressions )?
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
					// Pseudo.g:236:5: '[' ( expressions )? ']'
					{
					char_literal137=(Token)match(input,56,FOLLOW_56_in_atom_expr1426); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_56.add(char_literal137);

					// Pseudo.g:236:9: ( expressions )?
					int alt35=2;
					int LA35_0 = input.LA(1);
					if ( (LA35_0==BLOCK_BEGIN||LA35_0==ID||LA35_0==LIT||(LA35_0 >= MINUS && LA35_0 <= NOT)||LA35_0==51||LA35_0==56) ) {
						alt35=1;
					}
					switch (alt35) {
						case 1 :
							// Pseudo.g:236:9: expressions
							{
							pushFollow(FOLLOW_expressions_in_atom_expr1428);
							expressions138=expressions();
							state._fsp--;
							if (state.failed) return retval;
							if ( state.backtracking==0 ) stream_expressions.add(expressions138.getTree());
							}
							break;

					}

					char_literal139=(Token)match(input,57,FOLLOW_57_in_atom_expr1431); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_57.add(char_literal139);

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
					// 236:26: -> ^( LISTEX ( expressions )? )
					{
						// Pseudo.g:236:29: ^( LISTEX ( expressions )? )
						{
						PseudoTree root_1 = (PseudoTree)adaptor.nil();
						root_1 = (PseudoTree)adaptor.becomeRoot((PseudoTree)adaptor.create(LISTEX, "LISTEX"), root_1);
						// Pseudo.g:236:38: ( expressions )?
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
	// Pseudo.g:239:1: quantifier : '(' ! ( ALL ^| EX ^) ID ':' ! type '::' ! expression ')' !;
	public final PseudoParser.quantifier_return quantifier() throws RecognitionException {
		PseudoParser.quantifier_return retval = new PseudoParser.quantifier_return();
		retval.start = input.LT(1);

		PseudoTree root_0 = null;

		Token char_literal140=null;
		Token ALL141=null;
		Token EX142=null;
		Token ID143=null;
		Token char_literal144=null;
		Token string_literal146=null;
		Token char_literal148=null;
		ParserRuleReturnScope type145 =null;
		ParserRuleReturnScope expression147 =null;

		PseudoTree char_literal140_tree=null;
		PseudoTree ALL141_tree=null;
		PseudoTree EX142_tree=null;
		PseudoTree ID143_tree=null;
		PseudoTree char_literal144_tree=null;
		PseudoTree string_literal146_tree=null;
		PseudoTree char_literal148_tree=null;

		try {
			// Pseudo.g:239:11: ( '(' ! ( ALL ^| EX ^) ID ':' ! type '::' ! expression ')' !)
			// Pseudo.g:240:3: '(' ! ( ALL ^| EX ^) ID ':' ! type '::' ! expression ')' !
			{
			root_0 = (PseudoTree)adaptor.nil();


			char_literal140=(Token)match(input,51,FOLLOW_51_in_quantifier1452); if (state.failed) return retval;
			// Pseudo.g:240:8: ( ALL ^| EX ^)
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
					// Pseudo.g:240:9: ALL ^
					{
					ALL141=(Token)match(input,ALL,FOLLOW_ALL_in_quantifier1456); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					ALL141_tree = (PseudoTree)adaptor.create(ALL141);
					root_0 = (PseudoTree)adaptor.becomeRoot(ALL141_tree, root_0);
					}

					}
					break;
				case 2 :
					// Pseudo.g:240:16: EX ^
					{
					EX142=(Token)match(input,EX,FOLLOW_EX_in_quantifier1461); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					EX142_tree = (PseudoTree)adaptor.create(EX142);
					root_0 = (PseudoTree)adaptor.becomeRoot(EX142_tree, root_0);
					}

					}
					break;

			}

			ID143=(Token)match(input,ID,FOLLOW_ID_in_quantifier1465); if (state.failed) return retval;
			if ( state.backtracking==0 ) {
			ID143_tree = (PseudoTree)adaptor.create(ID143);
			adaptor.addChild(root_0, ID143_tree);
			}

			char_literal144=(Token)match(input,54,FOLLOW_54_in_quantifier1467); if (state.failed) return retval;
			pushFollow(FOLLOW_type_in_quantifier1470);
			type145=type();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, type145.getTree());

			string_literal146=(Token)match(input,DOUBLECOLON,FOLLOW_DOUBLECOLON_in_quantifier1472); if (state.failed) return retval;
			pushFollow(FOLLOW_expression_in_quantifier1475);
			expression147=expression();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, expression147.getTree());

			char_literal148=(Token)match(input,52,FOLLOW_52_in_quantifier1477); if (state.failed) return retval;
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
		// Pseudo.g:172:5: ( ID ':=' 'call' )
		// Pseudo.g:172:6: ID ':=' 'call'
		{
		match(input,ID,FOLLOW_ID_in_synpred1_Pseudo857); if (state.failed) return;

		match(input,ASSIGN,FOLLOW_ASSIGN_in_synpred1_Pseudo859); if (state.failed) return;

		match(input,CALL,FOLLOW_CALL_in_synpred1_Pseudo861); if (state.failed) return;

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



	public static final BitSet FOLLOW_method_in_program415 = new BitSet(new long[]{0x0000000800000002L});
	public static final BitSet FOLLOW_METHOD_in_method429 = new BitSet(new long[]{0x0000000001000000L});
	public static final BitSet FOLLOW_ID_in_method431 = new BitSet(new long[]{0x0008000000000000L});
	public static final BitSet FOLLOW_51_in_method433 = new BitSet(new long[]{0x0010000001000000L});
	public static final BitSet FOLLOW_vars_in_method435 = new BitSet(new long[]{0x0010000000000000L});
	public static final BitSet FOLLOW_52_in_method438 = new BitSet(new long[]{0x0000050000089000L});
	public static final BitSet FOLLOW_returns__in_method444 = new BitSet(new long[]{0x0000010000089000L});
	public static final BitSet FOLLOW_requires_in_method453 = new BitSet(new long[]{0x0000010000089000L});
	public static final BitSet FOLLOW_ensures_in_method462 = new BitSet(new long[]{0x0000000000089000L});
	public static final BitSet FOLLOW_decreases_in_method471 = new BitSet(new long[]{0x0000000000001000L});
	public static final BitSet FOLLOW_BLOCK_BEGIN_in_method478 = new BitSet(new long[]{0x0003000003002200L});
	public static final BitSet FOLLOW_decl_in_method482 = new BitSet(new long[]{0x0003000003002200L});
	public static final BitSet FOLLOW_statements_in_method487 = new BitSet(new long[]{0x0000000000002000L});
	public static final BitSet FOLLOW_BLOCK_END_in_method490 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_VAR_in_decl554 = new BitSet(new long[]{0x0000000001000000L});
	public static final BitSet FOLLOW_var_in_decl557 = new BitSet(new long[]{0x0080000000000000L});
	public static final BitSet FOLLOW_55_in_decl559 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_var_in_vars572 = new BitSet(new long[]{0x0020000000000002L});
	public static final BitSet FOLLOW_53_in_vars578 = new BitSet(new long[]{0x0000000001000000L});
	public static final BitSet FOLLOW_var_in_vars581 = new BitSet(new long[]{0x0020000000000002L});
	public static final BitSet FOLLOW_ID_in_var596 = new BitSet(new long[]{0x0040000000000000L});
	public static final BitSet FOLLOW_54_in_var598 = new BitSet(new long[]{0x0000080008000080L});
	public static final BitSet FOLLOW_type_in_var600 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_INT_in_type624 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_SET_in_type628 = new BitSet(new long[]{0x0000000400000000L});
	public static final BitSet FOLLOW_LT_in_type631 = new BitSet(new long[]{0x0000000008000000L});
	public static final BitSet FOLLOW_INT_in_type634 = new BitSet(new long[]{0x0000000000800000L});
	public static final BitSet FOLLOW_GT_in_type636 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_ARRAY_in_type643 = new BitSet(new long[]{0x0000000400000000L});
	public static final BitSet FOLLOW_LT_in_type646 = new BitSet(new long[]{0x0000000008000000L});
	public static final BitSet FOLLOW_INT_in_type649 = new BitSet(new long[]{0x0000000000800000L});
	public static final BitSet FOLLOW_GT_in_type651 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_RETURNS_in_returns_664 = new BitSet(new long[]{0x0008000000000000L});
	public static final BitSet FOLLOW_51_in_returns_667 = new BitSet(new long[]{0x0000000001000000L});
	public static final BitSet FOLLOW_vars_in_returns_670 = new BitSet(new long[]{0x0010000000000000L});
	public static final BitSet FOLLOW_52_in_returns_672 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_REQUIRES_in_requires685 = new BitSet(new long[]{0x0108003201001000L});
	public static final BitSet FOLLOW_ID_in_requires689 = new BitSet(new long[]{0x0040000000000000L});
	public static final BitSet FOLLOW_54_in_requires691 = new BitSet(new long[]{0x0108003201001000L});
	public static final BitSet FOLLOW_expression_in_requires696 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_ENSURES_in_ensures708 = new BitSet(new long[]{0x0108003201001000L});
	public static final BitSet FOLLOW_ID_in_ensures712 = new BitSet(new long[]{0x0040000000000000L});
	public static final BitSet FOLLOW_54_in_ensures714 = new BitSet(new long[]{0x0108003201001000L});
	public static final BitSet FOLLOW_expression_in_ensures719 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_DECREASES_in_decreases731 = new BitSet(new long[]{0x0108003201001000L});
	public static final BitSet FOLLOW_expression_in_decreases734 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_INVARIANT_in_invariant746 = new BitSet(new long[]{0x0108003201001000L});
	public static final BitSet FOLLOW_ID_in_invariant750 = new BitSet(new long[]{0x0040000000000000L});
	public static final BitSet FOLLOW_54_in_invariant752 = new BitSet(new long[]{0x0108003201001000L});
	public static final BitSet FOLLOW_expression_in_invariant757 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_BLOCK_BEGIN_in_block769 = new BitSet(new long[]{0x0002000003002200L});
	public static final BitSet FOLLOW_statements_in_block771 = new BitSet(new long[]{0x0000000000002000L});
	public static final BitSet FOLLOW_BLOCK_END_in_block774 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_block_in_relaxedBlock797 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_statement_in_relaxedBlock803 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_statement_in_statements825 = new BitSet(new long[]{0x0002000003000202L});
	public static final BitSet FOLLOW_ID_in_statement842 = new BitSet(new long[]{0x0000000000000400L});
	public static final BitSet FOLLOW_ASSIGN_in_statement844 = new BitSet(new long[]{0x0108003201001000L});
	public static final BitSet FOLLOW_expression_in_statement847 = new BitSet(new long[]{0x0080000000000000L});
	public static final BitSet FOLLOW_55_in_statement849 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_ID_in_statement868 = new BitSet(new long[]{0x0000000000000400L});
	public static final BitSet FOLLOW_ASSIGN_in_statement870 = new BitSet(new long[]{0x0000000000004000L});
	public static final BitSet FOLLOW_CALL_in_statement872 = new BitSet(new long[]{0x0000000001000000L});
	public static final BitSet FOLLOW_ID_in_statement876 = new BitSet(new long[]{0x0008000000000000L});
	public static final BitSet FOLLOW_51_in_statement878 = new BitSet(new long[]{0x0118003201001000L});
	public static final BitSet FOLLOW_expressions_in_statement880 = new BitSet(new long[]{0x0010000000000000L});
	public static final BitSet FOLLOW_52_in_statement883 = new BitSet(new long[]{0x0080000000000000L});
	public static final BitSet FOLLOW_55_in_statement885 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_ids_in_statement922 = new BitSet(new long[]{0x0000000000000400L});
	public static final BitSet FOLLOW_ASSIGN_in_statement924 = new BitSet(new long[]{0x0000000000004000L});
	public static final BitSet FOLLOW_CALL_in_statement926 = new BitSet(new long[]{0x0000000001000000L});
	public static final BitSet FOLLOW_ID_in_statement928 = new BitSet(new long[]{0x0008000000000000L});
	public static final BitSet FOLLOW_51_in_statement930 = new BitSet(new long[]{0x0118003201001000L});
	public static final BitSet FOLLOW_expressions_in_statement932 = new BitSet(new long[]{0x0010000000000000L});
	public static final BitSet FOLLOW_52_in_statement935 = new BitSet(new long[]{0x0080000000000000L});
	public static final BitSet FOLLOW_55_in_statement937 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_WHILE_in_statement972 = new BitSet(new long[]{0x0108003201001000L});
	public static final BitSet FOLLOW_expression_in_statement975 = new BitSet(new long[]{0x0000000020000000L});
	public static final BitSet FOLLOW_invariant_in_statement983 = new BitSet(new long[]{0x0000000020008000L});
	public static final BitSet FOLLOW_decreases_in_statement992 = new BitSet(new long[]{0x0002000003001200L});
	public static final BitSet FOLLOW_relaxedBlock_in_statement1000 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_IF_in_statement1006 = new BitSet(new long[]{0x0108003201001000L});
	public static final BitSet FOLLOW_expression_in_statement1009 = new BitSet(new long[]{0x0002000003001200L});
	public static final BitSet FOLLOW_relaxedBlock_in_statement1011 = new BitSet(new long[]{0x0000000000040002L});
	public static final BitSet FOLLOW_ELSE_in_statement1032 = new BitSet(new long[]{0x0002000003001200L});
	public static final BitSet FOLLOW_relaxedBlock_in_statement1035 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_ASSERT_in_statement1044 = new BitSet(new long[]{0x0108003201001000L});
	public static final BitSet FOLLOW_ID_in_statement1049 = new BitSet(new long[]{0x0040000000000000L});
	public static final BitSet FOLLOW_54_in_statement1051 = new BitSet(new long[]{0x0108003201001000L});
	public static final BitSet FOLLOW_expression_in_statement1057 = new BitSet(new long[]{0x0080000000000000L});
	public static final BitSet FOLLOW_55_in_statement1059 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_ID_in_ids1072 = new BitSet(new long[]{0x0020000000000000L});
	public static final BitSet FOLLOW_53_in_ids1075 = new BitSet(new long[]{0x0000000001000000L});
	public static final BitSet FOLLOW_ID_in_ids1078 = new BitSet(new long[]{0x0020000000000002L});
	public static final BitSet FOLLOW_expression_in_expressions1092 = new BitSet(new long[]{0x0020000000000002L});
	public static final BitSet FOLLOW_53_in_expressions1096 = new BitSet(new long[]{0x0108003201001000L});
	public static final BitSet FOLLOW_expression_in_expressions1099 = new BitSet(new long[]{0x0020000000000002L});
	public static final BitSet FOLLOW_or_expr_in_expression1114 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_and_expr_in_or_expr1123 = new BitSet(new long[]{0x0000004004000002L});
	public static final BitSet FOLLOW_OR_in_or_expr1128 = new BitSet(new long[]{0x0108003201001000L});
	public static final BitSet FOLLOW_IMPLIES_in_or_expr1133 = new BitSet(new long[]{0x0108003201001000L});
	public static final BitSet FOLLOW_or_expr_in_or_expr1137 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_rel_expr_in_and_expr1152 = new BitSet(new long[]{0x0000000000000022L});
	public static final BitSet FOLLOW_AND_in_and_expr1156 = new BitSet(new long[]{0x0108003201001000L});
	public static final BitSet FOLLOW_and_expr_in_and_expr1159 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_add_expr_in_rel_expr1174 = new BitSet(new long[]{0x0000000440D00002L});
	public static final BitSet FOLLOW_LT_in_rel_expr1179 = new BitSet(new long[]{0x0108003201001000L});
	public static final BitSet FOLLOW_GT_in_rel_expr1184 = new BitSet(new long[]{0x0108003201001000L});
	public static final BitSet FOLLOW_EQ_in_rel_expr1189 = new BitSet(new long[]{0x0108003201001000L});
	public static final BitSet FOLLOW_LE_in_rel_expr1194 = new BitSet(new long[]{0x0108003201001000L});
	public static final BitSet FOLLOW_GE_in_rel_expr1199 = new BitSet(new long[]{0x0108003201001000L});
	public static final BitSet FOLLOW_add_expr_in_rel_expr1203 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_mul_expr_in_add_expr1218 = new BitSet(new long[]{0x0000809000000002L});
	public static final BitSet FOLLOW_set_in_add_expr1222 = new BitSet(new long[]{0x0108003201001000L});
	public static final BitSet FOLLOW_add_expr_in_add_expr1235 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_prefix_expr_in_mul_expr1250 = new BitSet(new long[]{0x0000400010000002L});
	public static final BitSet FOLLOW_set_in_mul_expr1254 = new BitSet(new long[]{0x0108003201001000L});
	public static final BitSet FOLLOW_mul_expr_in_mul_expr1263 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_MINUS_in_prefix_expr1280 = new BitSet(new long[]{0x0108003201001000L});
	public static final BitSet FOLLOW_prefix_expr_in_prefix_expr1283 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_NOT_in_prefix_expr1289 = new BitSet(new long[]{0x0108003201001000L});
	public static final BitSet FOLLOW_prefix_expr_in_prefix_expr1292 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_postfix_expr_in_prefix_expr1298 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_atom_expr_in_postfix_expr1310 = new BitSet(new long[]{0x0100000000010002L});
	public static final BitSet FOLLOW_56_in_postfix_expr1316 = new BitSet(new long[]{0x0108003201001000L});
	public static final BitSet FOLLOW_expression_in_postfix_expr1318 = new BitSet(new long[]{0x0200000000000000L});
	public static final BitSet FOLLOW_57_in_postfix_expr1320 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_DOT_in_postfix_expr1338 = new BitSet(new long[]{0x0000000080000000L});
	public static final BitSet FOLLOW_LENGTH_in_postfix_expr1340 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_ID_in_atom_expr1376 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_LIT_in_atom_expr1382 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_quantifier_in_atom_expr1388 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_51_in_atom_expr1394 = new BitSet(new long[]{0x0108003201001000L});
	public static final BitSet FOLLOW_expression_in_atom_expr1397 = new BitSet(new long[]{0x0010000000000000L});
	public static final BitSet FOLLOW_52_in_atom_expr1399 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_BLOCK_BEGIN_in_atom_expr1406 = new BitSet(new long[]{0x0108003201003000L});
	public static final BitSet FOLLOW_expressions_in_atom_expr1408 = new BitSet(new long[]{0x0000000000002000L});
	public static final BitSet FOLLOW_BLOCK_END_in_atom_expr1411 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_56_in_atom_expr1426 = new BitSet(new long[]{0x0308003201001000L});
	public static final BitSet FOLLOW_expressions_in_atom_expr1428 = new BitSet(new long[]{0x0200000000000000L});
	public static final BitSet FOLLOW_57_in_atom_expr1431 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_51_in_quantifier1452 = new BitSet(new long[]{0x0000000000200010L});
	public static final BitSet FOLLOW_ALL_in_quantifier1456 = new BitSet(new long[]{0x0000000001000000L});
	public static final BitSet FOLLOW_EX_in_quantifier1461 = new BitSet(new long[]{0x0000000001000000L});
	public static final BitSet FOLLOW_ID_in_quantifier1465 = new BitSet(new long[]{0x0040000000000000L});
	public static final BitSet FOLLOW_54_in_quantifier1467 = new BitSet(new long[]{0x0000080008000080L});
	public static final BitSet FOLLOW_type_in_quantifier1470 = new BitSet(new long[]{0x0000000000020000L});
	public static final BitSet FOLLOW_DOUBLECOLON_in_quantifier1472 = new BitSet(new long[]{0x0108003201001000L});
	public static final BitSet FOLLOW_expression_in_quantifier1475 = new BitSet(new long[]{0x0010000000000000L});
	public static final BitSet FOLLOW_52_in_quantifier1477 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_ID_in_synpred1_Pseudo857 = new BitSet(new long[]{0x0000000000000400L});
	public static final BitSet FOLLOW_ASSIGN_in_synpred1_Pseudo859 = new BitSet(new long[]{0x0000000000004000L});
	public static final BitSet FOLLOW_CALL_in_synpred1_Pseudo861 = new BitSet(new long[]{0x0000000000000002L});
}
