// $ANTLR 3.5.1 Dafny.g 2016-06-07 10:22:58

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
		"ARRAY_ACCESS", "ASSERT", "ASSIGN", "ASSUME", "BLOCK", "BLOCK_BEGIN", 
		"BLOCK_END", "CALL", "DECREASES", "DOT", "DOUBLECOLON", "ELSE", "ENSURES", 
		"EQ", "EX", "FUNCTION", "GE", "GT", "ID", "IF", "IMPLIES", "INT", "INTERSECT", 
		"INVARIANT", "LABEL", "LE", "LEMMA", "LENGTH", "LISTEX", "LIT", "LT", 
		"METHOD", "MINUS", "MULTILINE_COMMENT", "NOT", "OR", "PLUS", "REQUIRES", 
		"RESULTS", "RETURNS", "SET", "SETEX", "SINGLELINE_COMMENT", "THEN", "TIMES", 
		"UNION", "VAR", "WHILE", "WS", "'('", "')'", "','", "':'", "';'", "'['", 
		"']'"
	};
	public static final int EOF=-1;
	public static final int T__57=57;
	public static final int T__58=58;
	public static final int T__59=59;
	public static final int T__60=60;
	public static final int T__61=61;
	public static final int T__62=62;
	public static final int T__63=63;
	public static final int ALL=4;
	public static final int AND=5;
	public static final int ARGS=6;
	public static final int ARRAY=7;
	public static final int ARRAY_ACCESS=8;
	public static final int ASSERT=9;
	public static final int ASSIGN=10;
	public static final int ASSUME=11;
	public static final int BLOCK=12;
	public static final int BLOCK_BEGIN=13;
	public static final int BLOCK_END=14;
	public static final int CALL=15;
	public static final int DECREASES=16;
	public static final int DOT=17;
	public static final int DOUBLECOLON=18;
	public static final int ELSE=19;
	public static final int ENSURES=20;
	public static final int EQ=21;
	public static final int EX=22;
	public static final int FUNCTION=23;
	public static final int GE=24;
	public static final int GT=25;
	public static final int ID=26;
	public static final int IF=27;
	public static final int IMPLIES=28;
	public static final int INT=29;
	public static final int INTERSECT=30;
	public static final int INVARIANT=31;
	public static final int LABEL=32;
	public static final int LE=33;
	public static final int LEMMA=34;
	public static final int LENGTH=35;
	public static final int LISTEX=36;
	public static final int LIT=37;
	public static final int LT=38;
	public static final int METHOD=39;
	public static final int MINUS=40;
	public static final int MULTILINE_COMMENT=41;
	public static final int NOT=42;
	public static final int OR=43;
	public static final int PLUS=44;
	public static final int REQUIRES=45;
	public static final int RESULTS=46;
	public static final int RETURNS=47;
	public static final int SET=48;
	public static final int SETEX=49;
	public static final int SINGLELINE_COMMENT=50;
	public static final int THEN=51;
	public static final int TIMES=52;
	public static final int UNION=53;
	public static final int VAR=54;
	public static final int WHILE=55;
	public static final int WS=56;

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


	public static class label_return extends ParserRuleReturnScope {
		DafnyTree tree;
		@Override
		public DafnyTree getTree() { return tree; }
	};


	// $ANTLR start "label"
	// Dafny.g:108:1: label : 'label' ^ ID ':' !;
	public final DafnyParser.label_return label() throws RecognitionException {
		DafnyParser.label_return retval = new DafnyParser.label_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		Token string_literal1=null;
		Token ID2=null;
		Token char_literal3=null;

		DafnyTree string_literal1_tree=null;
		DafnyTree ID2_tree=null;
		DafnyTree char_literal3_tree=null;

		try {
			// Dafny.g:108:6: ( 'label' ^ ID ':' !)
			// Dafny.g:109:3: 'label' ^ ID ':' !
			{
			root_0 = (DafnyTree)adaptor.nil();


			string_literal1=(Token)match(input,LABEL,FOLLOW_LABEL_in_label535); if (state.failed) return retval;
			if ( state.backtracking==0 ) {
			string_literal1_tree = (DafnyTree)adaptor.create(string_literal1);
			root_0 = (DafnyTree)adaptor.becomeRoot(string_literal1_tree, root_0);
			}

			ID2=(Token)match(input,ID,FOLLOW_ID_in_label538); if (state.failed) return retval;
			if ( state.backtracking==0 ) {
			ID2_tree = (DafnyTree)adaptor.create(ID2);
			adaptor.addChild(root_0, ID2_tree);
			}

			char_literal3=(Token)match(input,60,FOLLOW_60_in_label540); if (state.failed) return retval;
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
	// $ANTLR end "label"


	public static class program_return extends ParserRuleReturnScope {
		DafnyTree tree;
		@Override
		public DafnyTree getTree() { return tree; }
	};


	// $ANTLR start "program"
	// Dafny.g:112:1: program : ( method | function )+ ;
	public final DafnyParser.program_return program() throws RecognitionException {
		DafnyParser.program_return retval = new DafnyParser.program_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		ParserRuleReturnScope method4 =null;
		ParserRuleReturnScope function5 =null;


		try {
			// Dafny.g:112:8: ( ( method | function )+ )
			// Dafny.g:113:3: ( method | function )+
			{
			root_0 = (DafnyTree)adaptor.nil();


			// Dafny.g:113:3: ( method | function )+
			int cnt1=0;
			loop1:
			while (true) {
				int alt1=3;
				int LA1_0 = input.LA(1);
				if ( (LA1_0==LEMMA||LA1_0==METHOD) ) {
					alt1=1;
				}
				else if ( (LA1_0==FUNCTION) ) {
					alt1=2;
				}

				switch (alt1) {
				case 1 :
					// Dafny.g:113:4: method
					{
					pushFollow(FOLLOW_method_in_program554);
					method4=method();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, method4.getTree());

					}
					break;
				case 2 :
					// Dafny.g:113:13: function
					{
					pushFollow(FOLLOW_function_in_program558);
					function5=function();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, function5.getTree());

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
	// Dafny.g:116:1: method : tok= ( 'method' | 'lemma' ) ID '(' ( vars )? ')' ( returns_ )? ( requires )* ( ensures )* ( decreases )? '{' ( statements )? '}' -> ^( METHOD[tok] ID ^( ARGS ( vars )? ) ( returns_ )? ( requires )* ( ensures )* ( decreases )? ^( BLOCK ( statements )? ) ) ;
	public final DafnyParser.method_return method() throws RecognitionException {
		DafnyParser.method_return retval = new DafnyParser.method_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		Token tok=null;
		Token ID6=null;
		Token char_literal7=null;
		Token char_literal9=null;
		Token char_literal14=null;
		Token char_literal16=null;
		ParserRuleReturnScope vars8 =null;
		ParserRuleReturnScope returns_10 =null;
		ParserRuleReturnScope requires11 =null;
		ParserRuleReturnScope ensures12 =null;
		ParserRuleReturnScope decreases13 =null;
		ParserRuleReturnScope statements15 =null;

		DafnyTree tok_tree=null;
		DafnyTree ID6_tree=null;
		DafnyTree char_literal7_tree=null;
		DafnyTree char_literal9_tree=null;
		DafnyTree char_literal14_tree=null;
		DafnyTree char_literal16_tree=null;
		RewriteRuleTokenStream stream_58=new RewriteRuleTokenStream(adaptor,"token 58");
		RewriteRuleTokenStream stream_57=new RewriteRuleTokenStream(adaptor,"token 57");
		RewriteRuleTokenStream stream_ID=new RewriteRuleTokenStream(adaptor,"token ID");
		RewriteRuleTokenStream stream_BLOCK_BEGIN=new RewriteRuleTokenStream(adaptor,"token BLOCK_BEGIN");
		RewriteRuleTokenStream stream_LEMMA=new RewriteRuleTokenStream(adaptor,"token LEMMA");
		RewriteRuleTokenStream stream_METHOD=new RewriteRuleTokenStream(adaptor,"token METHOD");
		RewriteRuleTokenStream stream_BLOCK_END=new RewriteRuleTokenStream(adaptor,"token BLOCK_END");
		RewriteRuleSubtreeStream stream_returns_=new RewriteRuleSubtreeStream(adaptor,"rule returns_");
		RewriteRuleSubtreeStream stream_ensures=new RewriteRuleSubtreeStream(adaptor,"rule ensures");
		RewriteRuleSubtreeStream stream_vars=new RewriteRuleSubtreeStream(adaptor,"rule vars");
		RewriteRuleSubtreeStream stream_decreases=new RewriteRuleSubtreeStream(adaptor,"rule decreases");
		RewriteRuleSubtreeStream stream_statements=new RewriteRuleSubtreeStream(adaptor,"rule statements");
		RewriteRuleSubtreeStream stream_requires=new RewriteRuleSubtreeStream(adaptor,"rule requires");

		try {
			// Dafny.g:116:7: (tok= ( 'method' | 'lemma' ) ID '(' ( vars )? ')' ( returns_ )? ( requires )* ( ensures )* ( decreases )? '{' ( statements )? '}' -> ^( METHOD[tok] ID ^( ARGS ( vars )? ) ( returns_ )? ( requires )* ( ensures )* ( decreases )? ^( BLOCK ( statements )? ) ) )
			// Dafny.g:117:3: tok= ( 'method' | 'lemma' ) ID '(' ( vars )? ')' ( returns_ )? ( requires )* ( ensures )* ( decreases )? '{' ( statements )? '}'
			{
			// Dafny.g:117:9: ( 'method' | 'lemma' )
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
					// Dafny.g:117:10: 'method'
					{
					tok=(Token)match(input,METHOD,FOLLOW_METHOD_in_method577); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_METHOD.add(tok);

					}
					break;
				case 2 :
					// Dafny.g:117:21: 'lemma'
					{
					tok=(Token)match(input,LEMMA,FOLLOW_LEMMA_in_method581); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_LEMMA.add(tok);

					}
					break;

			}

			ID6=(Token)match(input,ID,FOLLOW_ID_in_method586); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_ID.add(ID6);

			char_literal7=(Token)match(input,57,FOLLOW_57_in_method588); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_57.add(char_literal7);

			// Dafny.g:118:10: ( vars )?
			int alt3=2;
			int LA3_0 = input.LA(1);
			if ( (LA3_0==ID) ) {
				alt3=1;
			}
			switch (alt3) {
				case 1 :
					// Dafny.g:118:10: vars
					{
					pushFollow(FOLLOW_vars_in_method590);
					vars8=vars();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_vars.add(vars8.getTree());
					}
					break;

			}

			char_literal9=(Token)match(input,58,FOLLOW_58_in_method593); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_58.add(char_literal9);

			// Dafny.g:119:3: ( returns_ )?
			int alt4=2;
			int LA4_0 = input.LA(1);
			if ( (LA4_0==RETURNS) ) {
				alt4=1;
			}
			switch (alt4) {
				case 1 :
					// Dafny.g:119:5: returns_
					{
					pushFollow(FOLLOW_returns__in_method599);
					returns_10=returns_();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_returns_.add(returns_10.getTree());
					}
					break;

			}

			// Dafny.g:120:3: ( requires )*
			loop5:
			while (true) {
				int alt5=2;
				int LA5_0 = input.LA(1);
				if ( (LA5_0==REQUIRES) ) {
					alt5=1;
				}

				switch (alt5) {
				case 1 :
					// Dafny.g:120:5: requires
					{
					pushFollow(FOLLOW_requires_in_method608);
					requires11=requires();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_requires.add(requires11.getTree());
					}
					break;

				default :
					break loop5;
				}
			}

			// Dafny.g:121:3: ( ensures )*
			loop6:
			while (true) {
				int alt6=2;
				int LA6_0 = input.LA(1);
				if ( (LA6_0==ENSURES) ) {
					alt6=1;
				}

				switch (alt6) {
				case 1 :
					// Dafny.g:121:5: ensures
					{
					pushFollow(FOLLOW_ensures_in_method617);
					ensures12=ensures();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_ensures.add(ensures12.getTree());
					}
					break;

				default :
					break loop6;
				}
			}

			// Dafny.g:122:3: ( decreases )?
			int alt7=2;
			int LA7_0 = input.LA(1);
			if ( (LA7_0==DECREASES) ) {
				alt7=1;
			}
			switch (alt7) {
				case 1 :
					// Dafny.g:122:5: decreases
					{
					pushFollow(FOLLOW_decreases_in_method626);
					decreases13=decreases();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_decreases.add(decreases13.getTree());
					}
					break;

			}

			char_literal14=(Token)match(input,BLOCK_BEGIN,FOLLOW_BLOCK_BEGIN_in_method633); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_BLOCK_BEGIN.add(char_literal14);

			// Dafny.g:123:7: ( statements )?
			int alt8=2;
			int LA8_0 = input.LA(1);
			if ( (LA8_0==ASSERT||LA8_0==ASSUME||(LA8_0 >= ID && LA8_0 <= IF)||LA8_0==LABEL||(LA8_0 >= VAR && LA8_0 <= WHILE)) ) {
				alt8=1;
			}
			switch (alt8) {
				case 1 :
					// Dafny.g:123:7: statements
					{
					pushFollow(FOLLOW_statements_in_method635);
					statements15=statements();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_statements.add(statements15.getTree());
					}
					break;

			}

			char_literal16=(Token)match(input,BLOCK_END,FOLLOW_BLOCK_END_in_method638); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_BLOCK_END.add(char_literal16);

			// AST REWRITE
			// elements: ensures, requires, decreases, ID, returns_, vars, statements
			// token labels: 
			// rule labels: retval
			// token list labels: 
			// rule list labels: 
			// wildcard labels: 
			if ( state.backtracking==0 ) {
			retval.tree = root_0;
			RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

			root_0 = (DafnyTree)adaptor.nil();
			// 124:3: -> ^( METHOD[tok] ID ^( ARGS ( vars )? ) ( returns_ )? ( requires )* ( ensures )* ( decreases )? ^( BLOCK ( statements )? ) )
			{
				// Dafny.g:125:5: ^( METHOD[tok] ID ^( ARGS ( vars )? ) ( returns_ )? ( requires )* ( ensures )* ( decreases )? ^( BLOCK ( statements )? ) )
				{
				DafnyTree root_1 = (DafnyTree)adaptor.nil();
				root_1 = (DafnyTree)adaptor.becomeRoot((DafnyTree)adaptor.create(METHOD, tok), root_1);
				adaptor.addChild(root_1, stream_ID.nextNode());
				// Dafny.g:125:22: ^( ARGS ( vars )? )
				{
				DafnyTree root_2 = (DafnyTree)adaptor.nil();
				root_2 = (DafnyTree)adaptor.becomeRoot((DafnyTree)adaptor.create(ARGS, "ARGS"), root_2);
				// Dafny.g:125:29: ( vars )?
				if ( stream_vars.hasNext() ) {
					adaptor.addChild(root_2, stream_vars.nextTree());
				}
				stream_vars.reset();

				adaptor.addChild(root_1, root_2);
				}

				// Dafny.g:125:36: ( returns_ )?
				if ( stream_returns_.hasNext() ) {
					adaptor.addChild(root_1, stream_returns_.nextTree());
				}
				stream_returns_.reset();

				// Dafny.g:125:46: ( requires )*
				while ( stream_requires.hasNext() ) {
					adaptor.addChild(root_1, stream_requires.nextTree());
				}
				stream_requires.reset();

				// Dafny.g:125:56: ( ensures )*
				while ( stream_ensures.hasNext() ) {
					adaptor.addChild(root_1, stream_ensures.nextTree());
				}
				stream_ensures.reset();

				// Dafny.g:126:9: ( decreases )?
				if ( stream_decreases.hasNext() ) {
					adaptor.addChild(root_1, stream_decreases.nextTree());
				}
				stream_decreases.reset();

				// Dafny.g:126:20: ^( BLOCK ( statements )? )
				{
				DafnyTree root_2 = (DafnyTree)adaptor.nil();
				root_2 = (DafnyTree)adaptor.becomeRoot((DafnyTree)adaptor.create(BLOCK, "BLOCK"), root_2);
				// Dafny.g:126:28: ( statements )?
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


	public static class function_return extends ParserRuleReturnScope {
		DafnyTree tree;
		@Override
		public DafnyTree getTree() { return tree; }
	};


	// $ANTLR start "function"
	// Dafny.g:129:1: function : 'function' ^ ID '(' ! ( vars )? ')' ! ':' ! type '{' ! expression '}' !;
	public final DafnyParser.function_return function() throws RecognitionException {
		DafnyParser.function_return retval = new DafnyParser.function_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		Token string_literal17=null;
		Token ID18=null;
		Token char_literal19=null;
		Token char_literal21=null;
		Token char_literal22=null;
		Token char_literal24=null;
		Token char_literal26=null;
		ParserRuleReturnScope vars20 =null;
		ParserRuleReturnScope type23 =null;
		ParserRuleReturnScope expression25 =null;

		DafnyTree string_literal17_tree=null;
		DafnyTree ID18_tree=null;
		DafnyTree char_literal19_tree=null;
		DafnyTree char_literal21_tree=null;
		DafnyTree char_literal22_tree=null;
		DafnyTree char_literal24_tree=null;
		DafnyTree char_literal26_tree=null;

		try {
			// Dafny.g:129:9: ( 'function' ^ ID '(' ! ( vars )? ')' ! ':' ! type '{' ! expression '}' !)
			// Dafny.g:130:3: 'function' ^ ID '(' ! ( vars )? ')' ! ':' ! type '{' ! expression '}' !
			{
			root_0 = (DafnyTree)adaptor.nil();


			string_literal17=(Token)match(input,FUNCTION,FOLLOW_FUNCTION_in_function700); if (state.failed) return retval;
			if ( state.backtracking==0 ) {
			string_literal17_tree = (DafnyTree)adaptor.create(string_literal17);
			root_0 = (DafnyTree)adaptor.becomeRoot(string_literal17_tree, root_0);
			}

			ID18=(Token)match(input,ID,FOLLOW_ID_in_function705); if (state.failed) return retval;
			if ( state.backtracking==0 ) {
			ID18_tree = (DafnyTree)adaptor.create(ID18);
			adaptor.addChild(root_0, ID18_tree);
			}

			char_literal19=(Token)match(input,57,FOLLOW_57_in_function707); if (state.failed) return retval;
			// Dafny.g:131:11: ( vars )?
			int alt9=2;
			int LA9_0 = input.LA(1);
			if ( (LA9_0==ID) ) {
				alt9=1;
			}
			switch (alt9) {
				case 1 :
					// Dafny.g:131:11: vars
					{
					pushFollow(FOLLOW_vars_in_function710);
					vars20=vars();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, vars20.getTree());

					}
					break;

			}

			char_literal21=(Token)match(input,58,FOLLOW_58_in_function713); if (state.failed) return retval;
			char_literal22=(Token)match(input,60,FOLLOW_60_in_function716); if (state.failed) return retval;
			pushFollow(FOLLOW_type_in_function719);
			type23=type();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, type23.getTree());

			char_literal24=(Token)match(input,BLOCK_BEGIN,FOLLOW_BLOCK_BEGIN_in_function723); if (state.failed) return retval;
			pushFollow(FOLLOW_expression_in_function726);
			expression25=expression();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, expression25.getTree());

			char_literal26=(Token)match(input,BLOCK_END,FOLLOW_BLOCK_END_in_function728); if (state.failed) return retval;
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
	// $ANTLR end "function"


	public static class vars_return extends ParserRuleReturnScope {
		DafnyTree tree;
		@Override
		public DafnyTree getTree() { return tree; }
	};


	// $ANTLR start "vars"
	// Dafny.g:135:1: vars : var ( ',' ! var )* ;
	public final DafnyParser.vars_return vars() throws RecognitionException {
		DafnyParser.vars_return retval = new DafnyParser.vars_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		Token char_literal28=null;
		ParserRuleReturnScope var27 =null;
		ParserRuleReturnScope var29 =null;

		DafnyTree char_literal28_tree=null;

		try {
			// Dafny.g:135:5: ( var ( ',' ! var )* )
			// Dafny.g:136:3: var ( ',' ! var )*
			{
			root_0 = (DafnyTree)adaptor.nil();


			pushFollow(FOLLOW_var_in_vars741);
			var27=var();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, var27.getTree());

			// Dafny.g:137:3: ( ',' ! var )*
			loop10:
			while (true) {
				int alt10=2;
				int LA10_0 = input.LA(1);
				if ( (LA10_0==59) ) {
					alt10=1;
				}

				switch (alt10) {
				case 1 :
					// Dafny.g:137:5: ',' ! var
					{
					char_literal28=(Token)match(input,59,FOLLOW_59_in_vars747); if (state.failed) return retval;
					pushFollow(FOLLOW_var_in_vars750);
					var29=var();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, var29.getTree());

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
	// Dafny.g:140:1: var : ID ':' type -> ^( VAR ID type ) ;
	public final DafnyParser.var_return var() throws RecognitionException {
		DafnyParser.var_return retval = new DafnyParser.var_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		Token ID30=null;
		Token char_literal31=null;
		ParserRuleReturnScope type32 =null;

		DafnyTree ID30_tree=null;
		DafnyTree char_literal31_tree=null;
		RewriteRuleTokenStream stream_ID=new RewriteRuleTokenStream(adaptor,"token ID");
		RewriteRuleTokenStream stream_60=new RewriteRuleTokenStream(adaptor,"token 60");
		RewriteRuleSubtreeStream stream_type=new RewriteRuleSubtreeStream(adaptor,"rule type");

		try {
			// Dafny.g:140:4: ( ID ':' type -> ^( VAR ID type ) )
			// Dafny.g:141:3: ID ':' type
			{
			ID30=(Token)match(input,ID,FOLLOW_ID_in_var765); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_ID.add(ID30);

			char_literal31=(Token)match(input,60,FOLLOW_60_in_var767); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_60.add(char_literal31);

			pushFollow(FOLLOW_type_in_var769);
			type32=type();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) stream_type.add(type32.getTree());
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
			// 141:15: -> ^( VAR ID type )
			{
				// Dafny.g:141:18: ^( VAR ID type )
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
	// Dafny.g:144:1: type : ( INT | SET ^ '<' ! INT '>' !| ARRAY ^ '<' ! INT '>' !);
	public final DafnyParser.type_return type() throws RecognitionException {
		DafnyParser.type_return retval = new DafnyParser.type_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		Token INT33=null;
		Token SET34=null;
		Token char_literal35=null;
		Token INT36=null;
		Token char_literal37=null;
		Token ARRAY38=null;
		Token char_literal39=null;
		Token INT40=null;
		Token char_literal41=null;

		DafnyTree INT33_tree=null;
		DafnyTree SET34_tree=null;
		DafnyTree char_literal35_tree=null;
		DafnyTree INT36_tree=null;
		DafnyTree char_literal37_tree=null;
		DafnyTree ARRAY38_tree=null;
		DafnyTree char_literal39_tree=null;
		DafnyTree INT40_tree=null;
		DafnyTree char_literal41_tree=null;

		try {
			// Dafny.g:144:5: ( INT | SET ^ '<' ! INT '>' !| ARRAY ^ '<' ! INT '>' !)
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
					// Dafny.g:145:5: INT
					{
					root_0 = (DafnyTree)adaptor.nil();


					INT33=(Token)match(input,INT,FOLLOW_INT_in_type793); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					INT33_tree = (DafnyTree)adaptor.create(INT33);
					adaptor.addChild(root_0, INT33_tree);
					}

					}
					break;
				case 2 :
					// Dafny.g:145:11: SET ^ '<' ! INT '>' !
					{
					root_0 = (DafnyTree)adaptor.nil();


					SET34=(Token)match(input,SET,FOLLOW_SET_in_type797); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					SET34_tree = (DafnyTree)adaptor.create(SET34);
					root_0 = (DafnyTree)adaptor.becomeRoot(SET34_tree, root_0);
					}

					char_literal35=(Token)match(input,LT,FOLLOW_LT_in_type800); if (state.failed) return retval;
					INT36=(Token)match(input,INT,FOLLOW_INT_in_type803); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					INT36_tree = (DafnyTree)adaptor.create(INT36);
					adaptor.addChild(root_0, INT36_tree);
					}

					char_literal37=(Token)match(input,GT,FOLLOW_GT_in_type805); if (state.failed) return retval;
					}
					break;
				case 3 :
					// Dafny.g:146:5: ARRAY ^ '<' ! INT '>' !
					{
					root_0 = (DafnyTree)adaptor.nil();


					ARRAY38=(Token)match(input,ARRAY,FOLLOW_ARRAY_in_type812); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					ARRAY38_tree = (DafnyTree)adaptor.create(ARRAY38);
					root_0 = (DafnyTree)adaptor.becomeRoot(ARRAY38_tree, root_0);
					}

					char_literal39=(Token)match(input,LT,FOLLOW_LT_in_type815); if (state.failed) return retval;
					INT40=(Token)match(input,INT,FOLLOW_INT_in_type818); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					INT40_tree = (DafnyTree)adaptor.create(INT40);
					adaptor.addChild(root_0, INT40_tree);
					}

					char_literal41=(Token)match(input,GT,FOLLOW_GT_in_type820); if (state.failed) return retval;
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
	// Dafny.g:149:1: returns_ : RETURNS ^ '(' ! vars ')' !;
	public final DafnyParser.returns__return returns_() throws RecognitionException {
		DafnyParser.returns__return retval = new DafnyParser.returns__return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		Token RETURNS42=null;
		Token char_literal43=null;
		Token char_literal45=null;
		ParserRuleReturnScope vars44 =null;

		DafnyTree RETURNS42_tree=null;
		DafnyTree char_literal43_tree=null;
		DafnyTree char_literal45_tree=null;

		try {
			// Dafny.g:149:9: ( RETURNS ^ '(' ! vars ')' !)
			// Dafny.g:150:3: RETURNS ^ '(' ! vars ')' !
			{
			root_0 = (DafnyTree)adaptor.nil();


			RETURNS42=(Token)match(input,RETURNS,FOLLOW_RETURNS_in_returns_833); if (state.failed) return retval;
			if ( state.backtracking==0 ) {
			RETURNS42_tree = (DafnyTree)adaptor.create(RETURNS42);
			root_0 = (DafnyTree)adaptor.becomeRoot(RETURNS42_tree, root_0);
			}

			char_literal43=(Token)match(input,57,FOLLOW_57_in_returns_836); if (state.failed) return retval;
			pushFollow(FOLLOW_vars_in_returns_839);
			vars44=vars();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, vars44.getTree());

			char_literal45=(Token)match(input,58,FOLLOW_58_in_returns_841); if (state.failed) return retval;
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
	// Dafny.g:153:1: requires : REQUIRES ^ ( label )? expression ;
	public final DafnyParser.requires_return requires() throws RecognitionException {
		DafnyParser.requires_return retval = new DafnyParser.requires_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		Token REQUIRES46=null;
		ParserRuleReturnScope label47 =null;
		ParserRuleReturnScope expression48 =null;

		DafnyTree REQUIRES46_tree=null;

		try {
			// Dafny.g:153:9: ( REQUIRES ^ ( label )? expression )
			// Dafny.g:154:3: REQUIRES ^ ( label )? expression
			{
			root_0 = (DafnyTree)adaptor.nil();


			REQUIRES46=(Token)match(input,REQUIRES,FOLLOW_REQUIRES_in_requires854); if (state.failed) return retval;
			if ( state.backtracking==0 ) {
			REQUIRES46_tree = (DafnyTree)adaptor.create(REQUIRES46);
			root_0 = (DafnyTree)adaptor.becomeRoot(REQUIRES46_tree, root_0);
			}

			// Dafny.g:154:13: ( label )?
			int alt12=2;
			int LA12_0 = input.LA(1);
			if ( (LA12_0==LABEL) ) {
				alt12=1;
			}
			switch (alt12) {
				case 1 :
					// Dafny.g:154:13: label
					{
					pushFollow(FOLLOW_label_in_requires857);
					label47=label();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, label47.getTree());

					}
					break;

			}

			pushFollow(FOLLOW_expression_in_requires860);
			expression48=expression();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, expression48.getTree());

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
	// Dafny.g:157:1: ensures : ENSURES ^ ( label )? expression ;
	public final DafnyParser.ensures_return ensures() throws RecognitionException {
		DafnyParser.ensures_return retval = new DafnyParser.ensures_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		Token ENSURES49=null;
		ParserRuleReturnScope label50 =null;
		ParserRuleReturnScope expression51 =null;

		DafnyTree ENSURES49_tree=null;

		try {
			// Dafny.g:157:8: ( ENSURES ^ ( label )? expression )
			// Dafny.g:158:3: ENSURES ^ ( label )? expression
			{
			root_0 = (DafnyTree)adaptor.nil();


			ENSURES49=(Token)match(input,ENSURES,FOLLOW_ENSURES_in_ensures872); if (state.failed) return retval;
			if ( state.backtracking==0 ) {
			ENSURES49_tree = (DafnyTree)adaptor.create(ENSURES49);
			root_0 = (DafnyTree)adaptor.becomeRoot(ENSURES49_tree, root_0);
			}

			// Dafny.g:158:12: ( label )?
			int alt13=2;
			int LA13_0 = input.LA(1);
			if ( (LA13_0==LABEL) ) {
				alt13=1;
			}
			switch (alt13) {
				case 1 :
					// Dafny.g:158:12: label
					{
					pushFollow(FOLLOW_label_in_ensures875);
					label50=label();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, label50.getTree());

					}
					break;

			}

			pushFollow(FOLLOW_expression_in_ensures878);
			expression51=expression();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, expression51.getTree());

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
	// Dafny.g:161:1: decreases : DECREASES ^ expression ;
	public final DafnyParser.decreases_return decreases() throws RecognitionException {
		DafnyParser.decreases_return retval = new DafnyParser.decreases_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		Token DECREASES52=null;
		ParserRuleReturnScope expression53 =null;

		DafnyTree DECREASES52_tree=null;

		try {
			// Dafny.g:161:10: ( DECREASES ^ expression )
			// Dafny.g:162:3: DECREASES ^ expression
			{
			root_0 = (DafnyTree)adaptor.nil();


			DECREASES52=(Token)match(input,DECREASES,FOLLOW_DECREASES_in_decreases890); if (state.failed) return retval;
			if ( state.backtracking==0 ) {
			DECREASES52_tree = (DafnyTree)adaptor.create(DECREASES52);
			root_0 = (DafnyTree)adaptor.becomeRoot(DECREASES52_tree, root_0);
			}

			pushFollow(FOLLOW_expression_in_decreases893);
			expression53=expression();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, expression53.getTree());

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
	// Dafny.g:165:1: invariant : INVARIANT ^ ( label )? expression ;
	public final DafnyParser.invariant_return invariant() throws RecognitionException {
		DafnyParser.invariant_return retval = new DafnyParser.invariant_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		Token INVARIANT54=null;
		ParserRuleReturnScope label55 =null;
		ParserRuleReturnScope expression56 =null;

		DafnyTree INVARIANT54_tree=null;

		try {
			// Dafny.g:165:10: ( INVARIANT ^ ( label )? expression )
			// Dafny.g:166:3: INVARIANT ^ ( label )? expression
			{
			root_0 = (DafnyTree)adaptor.nil();


			INVARIANT54=(Token)match(input,INVARIANT,FOLLOW_INVARIANT_in_invariant905); if (state.failed) return retval;
			if ( state.backtracking==0 ) {
			INVARIANT54_tree = (DafnyTree)adaptor.create(INVARIANT54);
			root_0 = (DafnyTree)adaptor.becomeRoot(INVARIANT54_tree, root_0);
			}

			// Dafny.g:166:14: ( label )?
			int alt14=2;
			int LA14_0 = input.LA(1);
			if ( (LA14_0==LABEL) ) {
				alt14=1;
			}
			switch (alt14) {
				case 1 :
					// Dafny.g:166:14: label
					{
					pushFollow(FOLLOW_label_in_invariant908);
					label55=label();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, label55.getTree());

					}
					break;

			}

			pushFollow(FOLLOW_expression_in_invariant911);
			expression56=expression();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, expression56.getTree());

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
	// Dafny.g:169:1: block : '{' ( statements )? '}' -> ^( BLOCK ( statements )? ) ;
	public final DafnyParser.block_return block() throws RecognitionException {
		DafnyParser.block_return retval = new DafnyParser.block_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		Token char_literal57=null;
		Token char_literal59=null;
		ParserRuleReturnScope statements58 =null;

		DafnyTree char_literal57_tree=null;
		DafnyTree char_literal59_tree=null;
		RewriteRuleTokenStream stream_BLOCK_BEGIN=new RewriteRuleTokenStream(adaptor,"token BLOCK_BEGIN");
		RewriteRuleTokenStream stream_BLOCK_END=new RewriteRuleTokenStream(adaptor,"token BLOCK_END");
		RewriteRuleSubtreeStream stream_statements=new RewriteRuleSubtreeStream(adaptor,"rule statements");

		try {
			// Dafny.g:169:6: ( '{' ( statements )? '}' -> ^( BLOCK ( statements )? ) )
			// Dafny.g:170:3: '{' ( statements )? '}'
			{
			char_literal57=(Token)match(input,BLOCK_BEGIN,FOLLOW_BLOCK_BEGIN_in_block923); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_BLOCK_BEGIN.add(char_literal57);

			// Dafny.g:170:7: ( statements )?
			int alt15=2;
			int LA15_0 = input.LA(1);
			if ( (LA15_0==ASSERT||LA15_0==ASSUME||(LA15_0 >= ID && LA15_0 <= IF)||LA15_0==LABEL||(LA15_0 >= VAR && LA15_0 <= WHILE)) ) {
				alt15=1;
			}
			switch (alt15) {
				case 1 :
					// Dafny.g:170:7: statements
					{
					pushFollow(FOLLOW_statements_in_block925);
					statements58=statements();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_statements.add(statements58.getTree());
					}
					break;

			}

			char_literal59=(Token)match(input,BLOCK_END,FOLLOW_BLOCK_END_in_block928); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_BLOCK_END.add(char_literal59);

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
			// 170:23: -> ^( BLOCK ( statements )? )
			{
				// Dafny.g:170:26: ^( BLOCK ( statements )? )
				{
				DafnyTree root_1 = (DafnyTree)adaptor.nil();
				root_1 = (DafnyTree)adaptor.becomeRoot((DafnyTree)adaptor.create(BLOCK, "BLOCK"), root_1);
				// Dafny.g:170:34: ( statements )?
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
	// Dafny.g:173:1: relaxedBlock : ( block | statement -> ^( BLOCK statement ) );
	public final DafnyParser.relaxedBlock_return relaxedBlock() throws RecognitionException {
		DafnyParser.relaxedBlock_return retval = new DafnyParser.relaxedBlock_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		ParserRuleReturnScope block60 =null;
		ParserRuleReturnScope statement61 =null;

		RewriteRuleSubtreeStream stream_statement=new RewriteRuleSubtreeStream(adaptor,"rule statement");

		try {
			// Dafny.g:173:13: ( block | statement -> ^( BLOCK statement ) )
			int alt16=2;
			int LA16_0 = input.LA(1);
			if ( (LA16_0==BLOCK_BEGIN) ) {
				alt16=1;
			}
			else if ( (LA16_0==ASSERT||LA16_0==ASSUME||(LA16_0 >= ID && LA16_0 <= IF)||LA16_0==LABEL||(LA16_0 >= VAR && LA16_0 <= WHILE)) ) {
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
					// Dafny.g:174:5: block
					{
					root_0 = (DafnyTree)adaptor.nil();


					pushFollow(FOLLOW_block_in_relaxedBlock951);
					block60=block();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, block60.getTree());

					}
					break;
				case 2 :
					// Dafny.g:175:5: statement
					{
					pushFollow(FOLLOW_statement_in_relaxedBlock957);
					statement61=statement();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_statement.add(statement61.getTree());
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
					// 175:15: -> ^( BLOCK statement )
					{
						// Dafny.g:175:18: ^( BLOCK statement )
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
	// Dafny.g:178:1: statements : ( statement )+ ;
	public final DafnyParser.statements_return statements() throws RecognitionException {
		DafnyParser.statements_return retval = new DafnyParser.statements_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		ParserRuleReturnScope statement62 =null;


		try {
			// Dafny.g:178:11: ( ( statement )+ )
			// Dafny.g:179:3: ( statement )+
			{
			root_0 = (DafnyTree)adaptor.nil();


			// Dafny.g:179:3: ( statement )+
			int cnt17=0;
			loop17:
			while (true) {
				int alt17=2;
				int LA17_0 = input.LA(1);
				if ( (LA17_0==ASSERT||LA17_0==ASSUME||(LA17_0 >= ID && LA17_0 <= IF)||LA17_0==LABEL||(LA17_0 >= VAR && LA17_0 <= WHILE)) ) {
					alt17=1;
				}

				switch (alt17) {
				case 1 :
					// Dafny.g:179:5: statement
					{
					pushFollow(FOLLOW_statement_in_statements979);
					statement62=statement();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, statement62.getTree());

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
	// Dafny.g:182:1: statement : ( VAR ^ ID ':' ! type ( ':=' ! expression )? ';' !| ID ':=' ^ expression ';' !| ( ID ':=' 'call' )=>r= ID ':=' 'call' f= ID '(' ( expressions )? ')' ';' -> ^( 'call' $f ^( RESULTS $r) ^( ARGS ( expressions )? ) ) | ids ':=' 'call' ID '(' ( expressions )? ')' ';' -> ^( 'call' ID ^( RESULTS ids ) ^( ARGS ( expressions )? ) ) | ( label )? 'while' expression ( invariant )+ decreases relaxedBlock -> ^( 'while' ( label )? expression ( invariant )+ decreases relaxedBlock ) | ( label )? 'if' ^ expression relaxedBlock ( options {greedy=true; } : 'else' ! relaxedBlock )? | 'assert' ^ ( 'label' ! ID ':' !)? expression ';' !| 'assume' ^ ( 'label' ! ID ':' !)? expression ';' !);
	public final DafnyParser.statement_return statement() throws RecognitionException {
		DafnyParser.statement_return retval = new DafnyParser.statement_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		Token r=null;
		Token f=null;
		Token VAR63=null;
		Token ID64=null;
		Token char_literal65=null;
		Token string_literal67=null;
		Token char_literal69=null;
		Token ID70=null;
		Token string_literal71=null;
		Token char_literal73=null;
		Token string_literal74=null;
		Token string_literal75=null;
		Token char_literal76=null;
		Token char_literal78=null;
		Token char_literal79=null;
		Token string_literal81=null;
		Token string_literal82=null;
		Token ID83=null;
		Token char_literal84=null;
		Token char_literal86=null;
		Token char_literal87=null;
		Token string_literal89=null;
		Token string_literal95=null;
		Token string_literal98=null;
		Token string_literal100=null;
		Token string_literal101=null;
		Token ID102=null;
		Token char_literal103=null;
		Token char_literal105=null;
		Token string_literal106=null;
		Token string_literal107=null;
		Token ID108=null;
		Token char_literal109=null;
		Token char_literal111=null;
		ParserRuleReturnScope type66 =null;
		ParserRuleReturnScope expression68 =null;
		ParserRuleReturnScope expression72 =null;
		ParserRuleReturnScope expressions77 =null;
		ParserRuleReturnScope ids80 =null;
		ParserRuleReturnScope expressions85 =null;
		ParserRuleReturnScope label88 =null;
		ParserRuleReturnScope expression90 =null;
		ParserRuleReturnScope invariant91 =null;
		ParserRuleReturnScope decreases92 =null;
		ParserRuleReturnScope relaxedBlock93 =null;
		ParserRuleReturnScope label94 =null;
		ParserRuleReturnScope expression96 =null;
		ParserRuleReturnScope relaxedBlock97 =null;
		ParserRuleReturnScope relaxedBlock99 =null;
		ParserRuleReturnScope expression104 =null;
		ParserRuleReturnScope expression110 =null;

		DafnyTree r_tree=null;
		DafnyTree f_tree=null;
		DafnyTree VAR63_tree=null;
		DafnyTree ID64_tree=null;
		DafnyTree char_literal65_tree=null;
		DafnyTree string_literal67_tree=null;
		DafnyTree char_literal69_tree=null;
		DafnyTree ID70_tree=null;
		DafnyTree string_literal71_tree=null;
		DafnyTree char_literal73_tree=null;
		DafnyTree string_literal74_tree=null;
		DafnyTree string_literal75_tree=null;
		DafnyTree char_literal76_tree=null;
		DafnyTree char_literal78_tree=null;
		DafnyTree char_literal79_tree=null;
		DafnyTree string_literal81_tree=null;
		DafnyTree string_literal82_tree=null;
		DafnyTree ID83_tree=null;
		DafnyTree char_literal84_tree=null;
		DafnyTree char_literal86_tree=null;
		DafnyTree char_literal87_tree=null;
		DafnyTree string_literal89_tree=null;
		DafnyTree string_literal95_tree=null;
		DafnyTree string_literal98_tree=null;
		DafnyTree string_literal100_tree=null;
		DafnyTree string_literal101_tree=null;
		DafnyTree ID102_tree=null;
		DafnyTree char_literal103_tree=null;
		DafnyTree char_literal105_tree=null;
		DafnyTree string_literal106_tree=null;
		DafnyTree string_literal107_tree=null;
		DafnyTree ID108_tree=null;
		DafnyTree char_literal109_tree=null;
		DafnyTree char_literal111_tree=null;
		RewriteRuleTokenStream stream_58=new RewriteRuleTokenStream(adaptor,"token 58");
		RewriteRuleTokenStream stream_CALL=new RewriteRuleTokenStream(adaptor,"token CALL");
		RewriteRuleTokenStream stream_57=new RewriteRuleTokenStream(adaptor,"token 57");
		RewriteRuleTokenStream stream_WHILE=new RewriteRuleTokenStream(adaptor,"token WHILE");
		RewriteRuleTokenStream stream_ID=new RewriteRuleTokenStream(adaptor,"token ID");
		RewriteRuleTokenStream stream_61=new RewriteRuleTokenStream(adaptor,"token 61");
		RewriteRuleTokenStream stream_ASSIGN=new RewriteRuleTokenStream(adaptor,"token ASSIGN");
		RewriteRuleSubtreeStream stream_expression=new RewriteRuleSubtreeStream(adaptor,"rule expression");
		RewriteRuleSubtreeStream stream_invariant=new RewriteRuleSubtreeStream(adaptor,"rule invariant");
		RewriteRuleSubtreeStream stream_decreases=new RewriteRuleSubtreeStream(adaptor,"rule decreases");
		RewriteRuleSubtreeStream stream_ids=new RewriteRuleSubtreeStream(adaptor,"rule ids");
		RewriteRuleSubtreeStream stream_label=new RewriteRuleSubtreeStream(adaptor,"rule label");
		RewriteRuleSubtreeStream stream_relaxedBlock=new RewriteRuleSubtreeStream(adaptor,"rule relaxedBlock");
		RewriteRuleSubtreeStream stream_expressions=new RewriteRuleSubtreeStream(adaptor,"rule expressions");

		try {
			// Dafny.g:182:10: ( VAR ^ ID ':' ! type ( ':=' ! expression )? ';' !| ID ':=' ^ expression ';' !| ( ID ':=' 'call' )=>r= ID ':=' 'call' f= ID '(' ( expressions )? ')' ';' -> ^( 'call' $f ^( RESULTS $r) ^( ARGS ( expressions )? ) ) | ids ':=' 'call' ID '(' ( expressions )? ')' ';' -> ^( 'call' ID ^( RESULTS ids ) ^( ARGS ( expressions )? ) ) | ( label )? 'while' expression ( invariant )+ decreases relaxedBlock -> ^( 'while' ( label )? expression ( invariant )+ decreases relaxedBlock ) | ( label )? 'if' ^ expression relaxedBlock ( options {greedy=true; } : 'else' ! relaxedBlock )? | 'assert' ^ ( 'label' ! ID ':' !)? expression ';' !| 'assume' ^ ( 'label' ! ID ':' !)? expression ';' !)
			int alt27=8;
			switch ( input.LA(1) ) {
			case VAR:
				{
				alt27=1;
				}
				break;
			case ID:
				{
				int LA27_2 = input.LA(2);
				if ( (LA27_2==ASSIGN) ) {
					int LA27_8 = input.LA(3);
					if ( (LA27_8==CALL) && (synpred1_Dafny())) {
						alt27=3;
					}
					else if ( (LA27_8==BLOCK_BEGIN||LA27_8==ID||LA27_8==LIT||LA27_8==MINUS||LA27_8==NOT||LA27_8==57||LA27_8==62) ) {
						alt27=2;
					}

					else {
						if (state.backtracking>0) {state.failed=true; return retval;}
						int nvaeMark = input.mark();
						try {
							for (int nvaeConsume = 0; nvaeConsume < 3 - 1; nvaeConsume++) {
								input.consume();
							}
							NoViableAltException nvae =
								new NoViableAltException("", 27, 8, input);
							throw nvae;
						} finally {
							input.rewind(nvaeMark);
						}
					}

				}
				else if ( (LA27_2==59) ) {
					alt27=4;
				}

				else {
					if (state.backtracking>0) {state.failed=true; return retval;}
					int nvaeMark = input.mark();
					try {
						input.consume();
						NoViableAltException nvae =
							new NoViableAltException("", 27, 2, input);
						throw nvae;
					} finally {
						input.rewind(nvaeMark);
					}
				}

				}
				break;
			case LABEL:
				{
				int LA27_3 = input.LA(2);
				if ( (LA27_3==ID) ) {
					int LA27_10 = input.LA(3);
					if ( (LA27_10==60) ) {
						int LA27_13 = input.LA(4);
						if ( (LA27_13==WHILE) ) {
							alt27=5;
						}
						else if ( (LA27_13==IF) ) {
							alt27=6;
						}

						else {
							if (state.backtracking>0) {state.failed=true; return retval;}
							int nvaeMark = input.mark();
							try {
								for (int nvaeConsume = 0; nvaeConsume < 4 - 1; nvaeConsume++) {
									input.consume();
								}
								NoViableAltException nvae =
									new NoViableAltException("", 27, 13, input);
								throw nvae;
							} finally {
								input.rewind(nvaeMark);
							}
						}

					}

					else {
						if (state.backtracking>0) {state.failed=true; return retval;}
						int nvaeMark = input.mark();
						try {
							for (int nvaeConsume = 0; nvaeConsume < 3 - 1; nvaeConsume++) {
								input.consume();
							}
							NoViableAltException nvae =
								new NoViableAltException("", 27, 10, input);
							throw nvae;
						} finally {
							input.rewind(nvaeMark);
						}
					}

				}

				else {
					if (state.backtracking>0) {state.failed=true; return retval;}
					int nvaeMark = input.mark();
					try {
						input.consume();
						NoViableAltException nvae =
							new NoViableAltException("", 27, 3, input);
						throw nvae;
					} finally {
						input.rewind(nvaeMark);
					}
				}

				}
				break;
			case WHILE:
				{
				alt27=5;
				}
				break;
			case IF:
				{
				alt27=6;
				}
				break;
			case ASSERT:
				{
				alt27=7;
				}
				break;
			case ASSUME:
				{
				alt27=8;
				}
				break;
			default:
				if (state.backtracking>0) {state.failed=true; return retval;}
				NoViableAltException nvae =
					new NoViableAltException("", 27, 0, input);
				throw nvae;
			}
			switch (alt27) {
				case 1 :
					// Dafny.g:183:5: VAR ^ ID ':' ! type ( ':=' ! expression )? ';' !
					{
					root_0 = (DafnyTree)adaptor.nil();


					VAR63=(Token)match(input,VAR,FOLLOW_VAR_in_statement996); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					VAR63_tree = (DafnyTree)adaptor.create(VAR63);
					root_0 = (DafnyTree)adaptor.becomeRoot(VAR63_tree, root_0);
					}

					ID64=(Token)match(input,ID,FOLLOW_ID_in_statement999); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					ID64_tree = (DafnyTree)adaptor.create(ID64);
					adaptor.addChild(root_0, ID64_tree);
					}

					char_literal65=(Token)match(input,60,FOLLOW_60_in_statement1001); if (state.failed) return retval;
					pushFollow(FOLLOW_type_in_statement1004);
					type66=type();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, type66.getTree());

					// Dafny.g:183:23: ( ':=' ! expression )?
					int alt18=2;
					int LA18_0 = input.LA(1);
					if ( (LA18_0==ASSIGN) ) {
						alt18=1;
					}
					switch (alt18) {
						case 1 :
							// Dafny.g:183:24: ':=' ! expression
							{
							string_literal67=(Token)match(input,ASSIGN,FOLLOW_ASSIGN_in_statement1007); if (state.failed) return retval;
							pushFollow(FOLLOW_expression_in_statement1010);
							expression68=expression();
							state._fsp--;
							if (state.failed) return retval;
							if ( state.backtracking==0 ) adaptor.addChild(root_0, expression68.getTree());

							}
							break;

					}

					char_literal69=(Token)match(input,61,FOLLOW_61_in_statement1014); if (state.failed) return retval;
					}
					break;
				case 2 :
					// Dafny.g:184:5: ID ':=' ^ expression ';' !
					{
					root_0 = (DafnyTree)adaptor.nil();


					ID70=(Token)match(input,ID,FOLLOW_ID_in_statement1021); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					ID70_tree = (DafnyTree)adaptor.create(ID70);
					adaptor.addChild(root_0, ID70_tree);
					}

					string_literal71=(Token)match(input,ASSIGN,FOLLOW_ASSIGN_in_statement1023); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					string_literal71_tree = (DafnyTree)adaptor.create(string_literal71);
					root_0 = (DafnyTree)adaptor.becomeRoot(string_literal71_tree, root_0);
					}

					pushFollow(FOLLOW_expression_in_statement1026);
					expression72=expression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, expression72.getTree());

					char_literal73=(Token)match(input,61,FOLLOW_61_in_statement1028); if (state.failed) return retval;
					}
					break;
				case 3 :
					// Dafny.g:185:5: ( ID ':=' 'call' )=>r= ID ':=' 'call' f= ID '(' ( expressions )? ')' ';'
					{
					r=(Token)match(input,ID,FOLLOW_ID_in_statement1047); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_ID.add(r);

					string_literal74=(Token)match(input,ASSIGN,FOLLOW_ASSIGN_in_statement1049); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_ASSIGN.add(string_literal74);

					string_literal75=(Token)match(input,CALL,FOLLOW_CALL_in_statement1051); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_CALL.add(string_literal75);

					f=(Token)match(input,ID,FOLLOW_ID_in_statement1055); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_ID.add(f);

					char_literal76=(Token)match(input,57,FOLLOW_57_in_statement1057); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_57.add(char_literal76);

					// Dafny.g:185:51: ( expressions )?
					int alt19=2;
					int LA19_0 = input.LA(1);
					if ( (LA19_0==BLOCK_BEGIN||LA19_0==ID||LA19_0==LIT||LA19_0==MINUS||LA19_0==NOT||LA19_0==57||LA19_0==62) ) {
						alt19=1;
					}
					switch (alt19) {
						case 1 :
							// Dafny.g:185:51: expressions
							{
							pushFollow(FOLLOW_expressions_in_statement1059);
							expressions77=expressions();
							state._fsp--;
							if (state.failed) return retval;
							if ( state.backtracking==0 ) stream_expressions.add(expressions77.getTree());
							}
							break;

					}

					char_literal78=(Token)match(input,58,FOLLOW_58_in_statement1062); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_58.add(char_literal78);

					char_literal79=(Token)match(input,61,FOLLOW_61_in_statement1064); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_61.add(char_literal79);

					// AST REWRITE
					// elements: CALL, expressions, r, f
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
					// 186:9: -> ^( 'call' $f ^( RESULTS $r) ^( ARGS ( expressions )? ) )
					{
						// Dafny.g:186:12: ^( 'call' $f ^( RESULTS $r) ^( ARGS ( expressions )? ) )
						{
						DafnyTree root_1 = (DafnyTree)adaptor.nil();
						root_1 = (DafnyTree)adaptor.becomeRoot(stream_CALL.nextNode(), root_1);
						adaptor.addChild(root_1, stream_f.nextNode());
						// Dafny.g:186:24: ^( RESULTS $r)
						{
						DafnyTree root_2 = (DafnyTree)adaptor.nil();
						root_2 = (DafnyTree)adaptor.becomeRoot((DafnyTree)adaptor.create(RESULTS, "RESULTS"), root_2);
						adaptor.addChild(root_2, stream_r.nextNode());
						adaptor.addChild(root_1, root_2);
						}

						// Dafny.g:186:38: ^( ARGS ( expressions )? )
						{
						DafnyTree root_2 = (DafnyTree)adaptor.nil();
						root_2 = (DafnyTree)adaptor.becomeRoot((DafnyTree)adaptor.create(ARGS, "ARGS"), root_2);
						// Dafny.g:186:45: ( expressions )?
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
					// Dafny.g:187:5: ids ':=' 'call' ID '(' ( expressions )? ')' ';'
					{
					pushFollow(FOLLOW_ids_in_statement1101);
					ids80=ids();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_ids.add(ids80.getTree());
					string_literal81=(Token)match(input,ASSIGN,FOLLOW_ASSIGN_in_statement1103); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_ASSIGN.add(string_literal81);

					string_literal82=(Token)match(input,CALL,FOLLOW_CALL_in_statement1105); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_CALL.add(string_literal82);

					ID83=(Token)match(input,ID,FOLLOW_ID_in_statement1107); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_ID.add(ID83);

					char_literal84=(Token)match(input,57,FOLLOW_57_in_statement1109); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_57.add(char_literal84);

					// Dafny.g:187:28: ( expressions )?
					int alt20=2;
					int LA20_0 = input.LA(1);
					if ( (LA20_0==BLOCK_BEGIN||LA20_0==ID||LA20_0==LIT||LA20_0==MINUS||LA20_0==NOT||LA20_0==57||LA20_0==62) ) {
						alt20=1;
					}
					switch (alt20) {
						case 1 :
							// Dafny.g:187:28: expressions
							{
							pushFollow(FOLLOW_expressions_in_statement1111);
							expressions85=expressions();
							state._fsp--;
							if (state.failed) return retval;
							if ( state.backtracking==0 ) stream_expressions.add(expressions85.getTree());
							}
							break;

					}

					char_literal86=(Token)match(input,58,FOLLOW_58_in_statement1114); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_58.add(char_literal86);

					char_literal87=(Token)match(input,61,FOLLOW_61_in_statement1116); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_61.add(char_literal87);

					// AST REWRITE
					// elements: ID, ids, CALL, expressions
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (DafnyTree)adaptor.nil();
					// 188:9: -> ^( 'call' ID ^( RESULTS ids ) ^( ARGS ( expressions )? ) )
					{
						// Dafny.g:188:12: ^( 'call' ID ^( RESULTS ids ) ^( ARGS ( expressions )? ) )
						{
						DafnyTree root_1 = (DafnyTree)adaptor.nil();
						root_1 = (DafnyTree)adaptor.becomeRoot(stream_CALL.nextNode(), root_1);
						adaptor.addChild(root_1, stream_ID.nextNode());
						// Dafny.g:188:24: ^( RESULTS ids )
						{
						DafnyTree root_2 = (DafnyTree)adaptor.nil();
						root_2 = (DafnyTree)adaptor.becomeRoot((DafnyTree)adaptor.create(RESULTS, "RESULTS"), root_2);
						adaptor.addChild(root_2, stream_ids.nextTree());
						adaptor.addChild(root_1, root_2);
						}

						// Dafny.g:188:39: ^( ARGS ( expressions )? )
						{
						DafnyTree root_2 = (DafnyTree)adaptor.nil();
						root_2 = (DafnyTree)adaptor.becomeRoot((DafnyTree)adaptor.create(ARGS, "ARGS"), root_2);
						// Dafny.g:188:46: ( expressions )?
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
				case 5 :
					// Dafny.g:189:5: ( label )? 'while' expression ( invariant )+ decreases relaxedBlock
					{
					// Dafny.g:189:5: ( label )?
					int alt21=2;
					int LA21_0 = input.LA(1);
					if ( (LA21_0==LABEL) ) {
						alt21=1;
					}
					switch (alt21) {
						case 1 :
							// Dafny.g:189:5: label
							{
							pushFollow(FOLLOW_label_in_statement1151);
							label88=label();
							state._fsp--;
							if (state.failed) return retval;
							if ( state.backtracking==0 ) stream_label.add(label88.getTree());
							}
							break;

					}

					string_literal89=(Token)match(input,WHILE,FOLLOW_WHILE_in_statement1160); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_WHILE.add(string_literal89);

					pushFollow(FOLLOW_expression_in_statement1162);
					expression90=expression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_expression.add(expression90.getTree());
					// Dafny.g:190:26: ( invariant )+
					int cnt22=0;
					loop22:
					while (true) {
						int alt22=2;
						int LA22_0 = input.LA(1);
						if ( (LA22_0==INVARIANT) ) {
							alt22=1;
						}

						switch (alt22) {
						case 1 :
							// Dafny.g:190:26: invariant
							{
							pushFollow(FOLLOW_invariant_in_statement1164);
							invariant91=invariant();
							state._fsp--;
							if (state.failed) return retval;
							if ( state.backtracking==0 ) stream_invariant.add(invariant91.getTree());
							}
							break;

						default :
							if ( cnt22 >= 1 ) break loop22;
							if (state.backtracking>0) {state.failed=true; return retval;}
							EarlyExitException eee = new EarlyExitException(22, input);
							throw eee;
						}
						cnt22++;
					}

					pushFollow(FOLLOW_decreases_in_statement1167);
					decreases92=decreases();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_decreases.add(decreases92.getTree());
					pushFollow(FOLLOW_relaxedBlock_in_statement1169);
					relaxedBlock93=relaxedBlock();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_relaxedBlock.add(relaxedBlock93.getTree());
					// AST REWRITE
					// elements: label, WHILE, invariant, expression, relaxedBlock, decreases
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (DafnyTree)adaptor.nil();
					// 191:9: -> ^( 'while' ( label )? expression ( invariant )+ decreases relaxedBlock )
					{
						// Dafny.g:191:12: ^( 'while' ( label )? expression ( invariant )+ decreases relaxedBlock )
						{
						DafnyTree root_1 = (DafnyTree)adaptor.nil();
						root_1 = (DafnyTree)adaptor.becomeRoot(stream_WHILE.nextNode(), root_1);
						// Dafny.g:191:22: ( label )?
						if ( stream_label.hasNext() ) {
							adaptor.addChild(root_1, stream_label.nextTree());
						}
						stream_label.reset();

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
				case 6 :
					// Dafny.g:192:5: ( label )? 'if' ^ expression relaxedBlock ( options {greedy=true; } : 'else' ! relaxedBlock )?
					{
					root_0 = (DafnyTree)adaptor.nil();


					// Dafny.g:192:5: ( label )?
					int alt23=2;
					int LA23_0 = input.LA(1);
					if ( (LA23_0==LABEL) ) {
						alt23=1;
					}
					switch (alt23) {
						case 1 :
							// Dafny.g:192:5: label
							{
							pushFollow(FOLLOW_label_in_statement1201);
							label94=label();
							state._fsp--;
							if (state.failed) return retval;
							if ( state.backtracking==0 ) adaptor.addChild(root_0, label94.getTree());

							}
							break;

					}

					string_literal95=(Token)match(input,IF,FOLLOW_IF_in_statement1204); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					string_literal95_tree = (DafnyTree)adaptor.create(string_literal95);
					root_0 = (DafnyTree)adaptor.becomeRoot(string_literal95_tree, root_0);
					}

					pushFollow(FOLLOW_expression_in_statement1207);
					expression96=expression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, expression96.getTree());

					pushFollow(FOLLOW_relaxedBlock_in_statement1209);
					relaxedBlock97=relaxedBlock();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, relaxedBlock97.getTree());

					// Dafny.g:193:7: ( options {greedy=true; } : 'else' ! relaxedBlock )?
					int alt24=2;
					int LA24_0 = input.LA(1);
					if ( (LA24_0==ELSE) ) {
						alt24=1;
					}
					switch (alt24) {
						case 1 :
							// Dafny.g:193:36: 'else' ! relaxedBlock
							{
							string_literal98=(Token)match(input,ELSE,FOLLOW_ELSE_in_statement1230); if (state.failed) return retval;
							pushFollow(FOLLOW_relaxedBlock_in_statement1233);
							relaxedBlock99=relaxedBlock();
							state._fsp--;
							if (state.failed) return retval;
							if ( state.backtracking==0 ) adaptor.addChild(root_0, relaxedBlock99.getTree());

							}
							break;

					}

					}
					break;
				case 7 :
					// Dafny.g:194:5: 'assert' ^ ( 'label' ! ID ':' !)? expression ';' !
					{
					root_0 = (DafnyTree)adaptor.nil();


					string_literal100=(Token)match(input,ASSERT,FOLLOW_ASSERT_in_statement1242); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					string_literal100_tree = (DafnyTree)adaptor.create(string_literal100);
					root_0 = (DafnyTree)adaptor.becomeRoot(string_literal100_tree, root_0);
					}

					// Dafny.g:194:15: ( 'label' ! ID ':' !)?
					int alt25=2;
					int LA25_0 = input.LA(1);
					if ( (LA25_0==LABEL) ) {
						alt25=1;
					}
					switch (alt25) {
						case 1 :
							// Dafny.g:194:17: 'label' ! ID ':' !
							{
							string_literal101=(Token)match(input,LABEL,FOLLOW_LABEL_in_statement1247); if (state.failed) return retval;
							ID102=(Token)match(input,ID,FOLLOW_ID_in_statement1250); if (state.failed) return retval;
							if ( state.backtracking==0 ) {
							ID102_tree = (DafnyTree)adaptor.create(ID102);
							adaptor.addChild(root_0, ID102_tree);
							}

							char_literal103=(Token)match(input,60,FOLLOW_60_in_statement1252); if (state.failed) return retval;
							}
							break;

					}

					pushFollow(FOLLOW_expression_in_statement1258);
					expression104=expression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, expression104.getTree());

					char_literal105=(Token)match(input,61,FOLLOW_61_in_statement1260); if (state.failed) return retval;
					}
					break;
				case 8 :
					// Dafny.g:195:5: 'assume' ^ ( 'label' ! ID ':' !)? expression ';' !
					{
					root_0 = (DafnyTree)adaptor.nil();


					string_literal106=(Token)match(input,ASSUME,FOLLOW_ASSUME_in_statement1267); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					string_literal106_tree = (DafnyTree)adaptor.create(string_literal106);
					root_0 = (DafnyTree)adaptor.becomeRoot(string_literal106_tree, root_0);
					}

					// Dafny.g:195:15: ( 'label' ! ID ':' !)?
					int alt26=2;
					int LA26_0 = input.LA(1);
					if ( (LA26_0==LABEL) ) {
						alt26=1;
					}
					switch (alt26) {
						case 1 :
							// Dafny.g:195:17: 'label' ! ID ':' !
							{
							string_literal107=(Token)match(input,LABEL,FOLLOW_LABEL_in_statement1272); if (state.failed) return retval;
							ID108=(Token)match(input,ID,FOLLOW_ID_in_statement1275); if (state.failed) return retval;
							if ( state.backtracking==0 ) {
							ID108_tree = (DafnyTree)adaptor.create(ID108);
							adaptor.addChild(root_0, ID108_tree);
							}

							char_literal109=(Token)match(input,60,FOLLOW_60_in_statement1277); if (state.failed) return retval;
							}
							break;

					}

					pushFollow(FOLLOW_expression_in_statement1283);
					expression110=expression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, expression110.getTree());

					char_literal111=(Token)match(input,61,FOLLOW_61_in_statement1285); if (state.failed) return retval;
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
	// Dafny.g:198:1: ids : ID ( ',' ! ID )+ ;
	public final DafnyParser.ids_return ids() throws RecognitionException {
		DafnyParser.ids_return retval = new DafnyParser.ids_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		Token ID112=null;
		Token char_literal113=null;
		Token ID114=null;

		DafnyTree ID112_tree=null;
		DafnyTree char_literal113_tree=null;
		DafnyTree ID114_tree=null;

		try {
			// Dafny.g:198:4: ( ID ( ',' ! ID )+ )
			// Dafny.g:199:3: ID ( ',' ! ID )+
			{
			root_0 = (DafnyTree)adaptor.nil();


			ID112=(Token)match(input,ID,FOLLOW_ID_in_ids1298); if (state.failed) return retval;
			if ( state.backtracking==0 ) {
			ID112_tree = (DafnyTree)adaptor.create(ID112);
			adaptor.addChild(root_0, ID112_tree);
			}

			// Dafny.g:199:6: ( ',' ! ID )+
			int cnt28=0;
			loop28:
			while (true) {
				int alt28=2;
				int LA28_0 = input.LA(1);
				if ( (LA28_0==59) ) {
					alt28=1;
				}

				switch (alt28) {
				case 1 :
					// Dafny.g:199:7: ',' ! ID
					{
					char_literal113=(Token)match(input,59,FOLLOW_59_in_ids1301); if (state.failed) return retval;
					ID114=(Token)match(input,ID,FOLLOW_ID_in_ids1304); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					ID114_tree = (DafnyTree)adaptor.create(ID114);
					adaptor.addChild(root_0, ID114_tree);
					}

					}
					break;

				default :
					if ( cnt28 >= 1 ) break loop28;
					if (state.backtracking>0) {state.failed=true; return retval;}
					EarlyExitException eee = new EarlyExitException(28, input);
					throw eee;
				}
				cnt28++;
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
	// Dafny.g:202:1: expressions : expression ( ',' ! expression )* ;
	public final DafnyParser.expressions_return expressions() throws RecognitionException {
		DafnyParser.expressions_return retval = new DafnyParser.expressions_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		Token char_literal116=null;
		ParserRuleReturnScope expression115 =null;
		ParserRuleReturnScope expression117 =null;

		DafnyTree char_literal116_tree=null;

		try {
			// Dafny.g:202:12: ( expression ( ',' ! expression )* )
			// Dafny.g:203:3: expression ( ',' ! expression )*
			{
			root_0 = (DafnyTree)adaptor.nil();


			pushFollow(FOLLOW_expression_in_expressions1318);
			expression115=expression();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, expression115.getTree());

			// Dafny.g:203:14: ( ',' ! expression )*
			loop29:
			while (true) {
				int alt29=2;
				int LA29_0 = input.LA(1);
				if ( (LA29_0==59) ) {
					alt29=1;
				}

				switch (alt29) {
				case 1 :
					// Dafny.g:203:16: ',' ! expression
					{
					char_literal116=(Token)match(input,59,FOLLOW_59_in_expressions1322); if (state.failed) return retval;
					pushFollow(FOLLOW_expression_in_expressions1325);
					expression117=expression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, expression117.getTree());

					}
					break;

				default :
					break loop29;
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
	// Dafny.g:206:1: expression : or_expr ;
	public final DafnyParser.expression_return expression() throws RecognitionException {
		DafnyParser.expression_return retval = new DafnyParser.expression_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		ParserRuleReturnScope or_expr118 =null;


		try {
			// Dafny.g:206:11: ( or_expr )
			// Dafny.g:207:3: or_expr
			{
			root_0 = (DafnyTree)adaptor.nil();


			pushFollow(FOLLOW_or_expr_in_expression1340);
			or_expr118=or_expr();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, or_expr118.getTree());

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
	// Dafny.g:209:1: or_expr : and_expr ( ( '||' ^| '==>' ^) or_expr )? ;
	public final DafnyParser.or_expr_return or_expr() throws RecognitionException {
		DafnyParser.or_expr_return retval = new DafnyParser.or_expr_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		Token string_literal120=null;
		Token string_literal121=null;
		ParserRuleReturnScope and_expr119 =null;
		ParserRuleReturnScope or_expr122 =null;

		DafnyTree string_literal120_tree=null;
		DafnyTree string_literal121_tree=null;

		try {
			// Dafny.g:209:8: ( and_expr ( ( '||' ^| '==>' ^) or_expr )? )
			// Dafny.g:210:3: and_expr ( ( '||' ^| '==>' ^) or_expr )?
			{
			root_0 = (DafnyTree)adaptor.nil();


			pushFollow(FOLLOW_and_expr_in_or_expr1349);
			and_expr119=and_expr();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, and_expr119.getTree());

			// Dafny.g:210:12: ( ( '||' ^| '==>' ^) or_expr )?
			int alt31=2;
			int LA31_0 = input.LA(1);
			if ( (LA31_0==IMPLIES||LA31_0==OR) ) {
				alt31=1;
			}
			switch (alt31) {
				case 1 :
					// Dafny.g:210:14: ( '||' ^| '==>' ^) or_expr
					{
					// Dafny.g:210:14: ( '||' ^| '==>' ^)
					int alt30=2;
					int LA30_0 = input.LA(1);
					if ( (LA30_0==OR) ) {
						alt30=1;
					}
					else if ( (LA30_0==IMPLIES) ) {
						alt30=2;
					}

					else {
						if (state.backtracking>0) {state.failed=true; return retval;}
						NoViableAltException nvae =
							new NoViableAltException("", 30, 0, input);
						throw nvae;
					}

					switch (alt30) {
						case 1 :
							// Dafny.g:210:15: '||' ^
							{
							string_literal120=(Token)match(input,OR,FOLLOW_OR_in_or_expr1354); if (state.failed) return retval;
							if ( state.backtracking==0 ) {
							string_literal120_tree = (DafnyTree)adaptor.create(string_literal120);
							root_0 = (DafnyTree)adaptor.becomeRoot(string_literal120_tree, root_0);
							}

							}
							break;
						case 2 :
							// Dafny.g:210:23: '==>' ^
							{
							string_literal121=(Token)match(input,IMPLIES,FOLLOW_IMPLIES_in_or_expr1359); if (state.failed) return retval;
							if ( state.backtracking==0 ) {
							string_literal121_tree = (DafnyTree)adaptor.create(string_literal121);
							root_0 = (DafnyTree)adaptor.becomeRoot(string_literal121_tree, root_0);
							}

							}
							break;

					}

					pushFollow(FOLLOW_or_expr_in_or_expr1363);
					or_expr122=or_expr();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, or_expr122.getTree());

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
	// Dafny.g:213:1: and_expr : rel_expr ( '&&' ^ and_expr )? ;
	public final DafnyParser.and_expr_return and_expr() throws RecognitionException {
		DafnyParser.and_expr_return retval = new DafnyParser.and_expr_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		Token string_literal124=null;
		ParserRuleReturnScope rel_expr123 =null;
		ParserRuleReturnScope and_expr125 =null;

		DafnyTree string_literal124_tree=null;

		try {
			// Dafny.g:213:9: ( rel_expr ( '&&' ^ and_expr )? )
			// Dafny.g:214:3: rel_expr ( '&&' ^ and_expr )?
			{
			root_0 = (DafnyTree)adaptor.nil();


			pushFollow(FOLLOW_rel_expr_in_and_expr1378);
			rel_expr123=rel_expr();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, rel_expr123.getTree());

			// Dafny.g:214:12: ( '&&' ^ and_expr )?
			int alt32=2;
			int LA32_0 = input.LA(1);
			if ( (LA32_0==AND) ) {
				alt32=1;
			}
			switch (alt32) {
				case 1 :
					// Dafny.g:214:14: '&&' ^ and_expr
					{
					string_literal124=(Token)match(input,AND,FOLLOW_AND_in_and_expr1382); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					string_literal124_tree = (DafnyTree)adaptor.create(string_literal124);
					root_0 = (DafnyTree)adaptor.becomeRoot(string_literal124_tree, root_0);
					}

					pushFollow(FOLLOW_and_expr_in_and_expr1385);
					and_expr125=and_expr();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, and_expr125.getTree());

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
	// Dafny.g:217:1: rel_expr : add_expr ( ( '<' ^| '>' ^| '==' ^| '<=' ^| '>=' ^) add_expr )? ;
	public final DafnyParser.rel_expr_return rel_expr() throws RecognitionException {
		DafnyParser.rel_expr_return retval = new DafnyParser.rel_expr_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		Token char_literal127=null;
		Token char_literal128=null;
		Token string_literal129=null;
		Token string_literal130=null;
		Token string_literal131=null;
		ParserRuleReturnScope add_expr126 =null;
		ParserRuleReturnScope add_expr132 =null;

		DafnyTree char_literal127_tree=null;
		DafnyTree char_literal128_tree=null;
		DafnyTree string_literal129_tree=null;
		DafnyTree string_literal130_tree=null;
		DafnyTree string_literal131_tree=null;

		try {
			// Dafny.g:217:9: ( add_expr ( ( '<' ^| '>' ^| '==' ^| '<=' ^| '>=' ^) add_expr )? )
			// Dafny.g:218:3: add_expr ( ( '<' ^| '>' ^| '==' ^| '<=' ^| '>=' ^) add_expr )?
			{
			root_0 = (DafnyTree)adaptor.nil();


			pushFollow(FOLLOW_add_expr_in_rel_expr1400);
			add_expr126=add_expr();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, add_expr126.getTree());

			// Dafny.g:218:12: ( ( '<' ^| '>' ^| '==' ^| '<=' ^| '>=' ^) add_expr )?
			int alt34=2;
			int LA34_0 = input.LA(1);
			if ( (LA34_0==EQ||(LA34_0 >= GE && LA34_0 <= GT)||LA34_0==LE||LA34_0==LT) ) {
				alt34=1;
			}
			switch (alt34) {
				case 1 :
					// Dafny.g:218:14: ( '<' ^| '>' ^| '==' ^| '<=' ^| '>=' ^) add_expr
					{
					// Dafny.g:218:14: ( '<' ^| '>' ^| '==' ^| '<=' ^| '>=' ^)
					int alt33=5;
					switch ( input.LA(1) ) {
					case LT:
						{
						alt33=1;
						}
						break;
					case GT:
						{
						alt33=2;
						}
						break;
					case EQ:
						{
						alt33=3;
						}
						break;
					case LE:
						{
						alt33=4;
						}
						break;
					case GE:
						{
						alt33=5;
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
							// Dafny.g:218:15: '<' ^
							{
							char_literal127=(Token)match(input,LT,FOLLOW_LT_in_rel_expr1405); if (state.failed) return retval;
							if ( state.backtracking==0 ) {
							char_literal127_tree = (DafnyTree)adaptor.create(char_literal127);
							root_0 = (DafnyTree)adaptor.becomeRoot(char_literal127_tree, root_0);
							}

							}
							break;
						case 2 :
							// Dafny.g:218:22: '>' ^
							{
							char_literal128=(Token)match(input,GT,FOLLOW_GT_in_rel_expr1410); if (state.failed) return retval;
							if ( state.backtracking==0 ) {
							char_literal128_tree = (DafnyTree)adaptor.create(char_literal128);
							root_0 = (DafnyTree)adaptor.becomeRoot(char_literal128_tree, root_0);
							}

							}
							break;
						case 3 :
							// Dafny.g:218:29: '==' ^
							{
							string_literal129=(Token)match(input,EQ,FOLLOW_EQ_in_rel_expr1415); if (state.failed) return retval;
							if ( state.backtracking==0 ) {
							string_literal129_tree = (DafnyTree)adaptor.create(string_literal129);
							root_0 = (DafnyTree)adaptor.becomeRoot(string_literal129_tree, root_0);
							}

							}
							break;
						case 4 :
							// Dafny.g:218:37: '<=' ^
							{
							string_literal130=(Token)match(input,LE,FOLLOW_LE_in_rel_expr1420); if (state.failed) return retval;
							if ( state.backtracking==0 ) {
							string_literal130_tree = (DafnyTree)adaptor.create(string_literal130);
							root_0 = (DafnyTree)adaptor.becomeRoot(string_literal130_tree, root_0);
							}

							}
							break;
						case 5 :
							// Dafny.g:218:45: '>=' ^
							{
							string_literal131=(Token)match(input,GE,FOLLOW_GE_in_rel_expr1425); if (state.failed) return retval;
							if ( state.backtracking==0 ) {
							string_literal131_tree = (DafnyTree)adaptor.create(string_literal131);
							root_0 = (DafnyTree)adaptor.becomeRoot(string_literal131_tree, root_0);
							}

							}
							break;

					}

					pushFollow(FOLLOW_add_expr_in_rel_expr1429);
					add_expr132=add_expr();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, add_expr132.getTree());

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
	// Dafny.g:221:1: add_expr : mul_expr ( ( '+' | '-' | '++' ) ^ add_expr )? ;
	public final DafnyParser.add_expr_return add_expr() throws RecognitionException {
		DafnyParser.add_expr_return retval = new DafnyParser.add_expr_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		Token set134=null;
		ParserRuleReturnScope mul_expr133 =null;
		ParserRuleReturnScope add_expr135 =null;

		DafnyTree set134_tree=null;

		try {
			// Dafny.g:221:9: ( mul_expr ( ( '+' | '-' | '++' ) ^ add_expr )? )
			// Dafny.g:222:3: mul_expr ( ( '+' | '-' | '++' ) ^ add_expr )?
			{
			root_0 = (DafnyTree)adaptor.nil();


			pushFollow(FOLLOW_mul_expr_in_add_expr1444);
			mul_expr133=mul_expr();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, mul_expr133.getTree());

			// Dafny.g:222:12: ( ( '+' | '-' | '++' ) ^ add_expr )?
			int alt35=2;
			int LA35_0 = input.LA(1);
			if ( (LA35_0==MINUS||LA35_0==PLUS||LA35_0==UNION) ) {
				alt35=1;
			}
			switch (alt35) {
				case 1 :
					// Dafny.g:222:14: ( '+' | '-' | '++' ) ^ add_expr
					{
					set134=input.LT(1);
					set134=input.LT(1);
					if ( input.LA(1)==MINUS||input.LA(1)==PLUS||input.LA(1)==UNION ) {
						input.consume();
						if ( state.backtracking==0 ) root_0 = (DafnyTree)adaptor.becomeRoot((DafnyTree)adaptor.create(set134), root_0);
						state.errorRecovery=false;
						state.failed=false;
					}
					else {
						if (state.backtracking>0) {state.failed=true; return retval;}
						MismatchedSetException mse = new MismatchedSetException(null,input);
						throw mse;
					}
					pushFollow(FOLLOW_add_expr_in_add_expr1461);
					add_expr135=add_expr();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, add_expr135.getTree());

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
	// Dafny.g:225:1: mul_expr : prefix_expr ( ( '*' | '**' ) ^ mul_expr )? ;
	public final DafnyParser.mul_expr_return mul_expr() throws RecognitionException {
		DafnyParser.mul_expr_return retval = new DafnyParser.mul_expr_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		Token set137=null;
		ParserRuleReturnScope prefix_expr136 =null;
		ParserRuleReturnScope mul_expr138 =null;

		DafnyTree set137_tree=null;

		try {
			// Dafny.g:225:9: ( prefix_expr ( ( '*' | '**' ) ^ mul_expr )? )
			// Dafny.g:226:3: prefix_expr ( ( '*' | '**' ) ^ mul_expr )?
			{
			root_0 = (DafnyTree)adaptor.nil();


			pushFollow(FOLLOW_prefix_expr_in_mul_expr1476);
			prefix_expr136=prefix_expr();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, prefix_expr136.getTree());

			// Dafny.g:226:15: ( ( '*' | '**' ) ^ mul_expr )?
			int alt36=2;
			int LA36_0 = input.LA(1);
			if ( (LA36_0==INTERSECT||LA36_0==TIMES) ) {
				alt36=1;
			}
			switch (alt36) {
				case 1 :
					// Dafny.g:226:17: ( '*' | '**' ) ^ mul_expr
					{
					set137=input.LT(1);
					set137=input.LT(1);
					if ( input.LA(1)==INTERSECT||input.LA(1)==TIMES ) {
						input.consume();
						if ( state.backtracking==0 ) root_0 = (DafnyTree)adaptor.becomeRoot((DafnyTree)adaptor.create(set137), root_0);
						state.errorRecovery=false;
						state.failed=false;
					}
					else {
						if (state.backtracking>0) {state.failed=true; return retval;}
						MismatchedSetException mse = new MismatchedSetException(null,input);
						throw mse;
					}
					pushFollow(FOLLOW_mul_expr_in_mul_expr1489);
					mul_expr138=mul_expr();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, mul_expr138.getTree());

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
	// Dafny.g:229:1: prefix_expr : ( '-' ^ prefix_expr | '!' ^ prefix_expr | postfix_expr );
	public final DafnyParser.prefix_expr_return prefix_expr() throws RecognitionException {
		DafnyParser.prefix_expr_return retval = new DafnyParser.prefix_expr_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		Token char_literal139=null;
		Token char_literal141=null;
		ParserRuleReturnScope prefix_expr140 =null;
		ParserRuleReturnScope prefix_expr142 =null;
		ParserRuleReturnScope postfix_expr143 =null;

		DafnyTree char_literal139_tree=null;
		DafnyTree char_literal141_tree=null;

		try {
			// Dafny.g:229:12: ( '-' ^ prefix_expr | '!' ^ prefix_expr | postfix_expr )
			int alt37=3;
			switch ( input.LA(1) ) {
			case MINUS:
				{
				alt37=1;
				}
				break;
			case NOT:
				{
				alt37=2;
				}
				break;
			case BLOCK_BEGIN:
			case ID:
			case LIT:
			case 57:
			case 62:
				{
				alt37=3;
				}
				break;
			default:
				if (state.backtracking>0) {state.failed=true; return retval;}
				NoViableAltException nvae =
					new NoViableAltException("", 37, 0, input);
				throw nvae;
			}
			switch (alt37) {
				case 1 :
					// Dafny.g:230:5: '-' ^ prefix_expr
					{
					root_0 = (DafnyTree)adaptor.nil();


					char_literal139=(Token)match(input,MINUS,FOLLOW_MINUS_in_prefix_expr1506); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					char_literal139_tree = (DafnyTree)adaptor.create(char_literal139);
					root_0 = (DafnyTree)adaptor.becomeRoot(char_literal139_tree, root_0);
					}

					pushFollow(FOLLOW_prefix_expr_in_prefix_expr1509);
					prefix_expr140=prefix_expr();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, prefix_expr140.getTree());

					}
					break;
				case 2 :
					// Dafny.g:231:5: '!' ^ prefix_expr
					{
					root_0 = (DafnyTree)adaptor.nil();


					char_literal141=(Token)match(input,NOT,FOLLOW_NOT_in_prefix_expr1515); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					char_literal141_tree = (DafnyTree)adaptor.create(char_literal141);
					root_0 = (DafnyTree)adaptor.becomeRoot(char_literal141_tree, root_0);
					}

					pushFollow(FOLLOW_prefix_expr_in_prefix_expr1518);
					prefix_expr142=prefix_expr();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, prefix_expr142.getTree());

					}
					break;
				case 3 :
					// Dafny.g:232:5: postfix_expr
					{
					root_0 = (DafnyTree)adaptor.nil();


					pushFollow(FOLLOW_postfix_expr_in_prefix_expr1524);
					postfix_expr143=postfix_expr();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, postfix_expr143.getTree());

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
	// Dafny.g:235:1: postfix_expr : atom_expr ( '[' expression ']' -> ^( ARRAY_ACCESS atom_expr expression ) | '.' LENGTH -> ^( LENGTH atom_expr ) | -> atom_expr | EOF -> atom_expr ) ;
	public final DafnyParser.postfix_expr_return postfix_expr() throws RecognitionException {
		DafnyParser.postfix_expr_return retval = new DafnyParser.postfix_expr_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		Token char_literal145=null;
		Token char_literal147=null;
		Token char_literal148=null;
		Token LENGTH149=null;
		Token EOF150=null;
		ParserRuleReturnScope atom_expr144 =null;
		ParserRuleReturnScope expression146 =null;

		DafnyTree char_literal145_tree=null;
		DafnyTree char_literal147_tree=null;
		DafnyTree char_literal148_tree=null;
		DafnyTree LENGTH149_tree=null;
		DafnyTree EOF150_tree=null;
		RewriteRuleTokenStream stream_DOT=new RewriteRuleTokenStream(adaptor,"token DOT");
		RewriteRuleTokenStream stream_EOF=new RewriteRuleTokenStream(adaptor,"token EOF");
		RewriteRuleTokenStream stream_62=new RewriteRuleTokenStream(adaptor,"token 62");
		RewriteRuleTokenStream stream_63=new RewriteRuleTokenStream(adaptor,"token 63");
		RewriteRuleTokenStream stream_LENGTH=new RewriteRuleTokenStream(adaptor,"token LENGTH");
		RewriteRuleSubtreeStream stream_expression=new RewriteRuleSubtreeStream(adaptor,"rule expression");
		RewriteRuleSubtreeStream stream_atom_expr=new RewriteRuleSubtreeStream(adaptor,"rule atom_expr");

		try {
			// Dafny.g:235:13: ( atom_expr ( '[' expression ']' -> ^( ARRAY_ACCESS atom_expr expression ) | '.' LENGTH -> ^( LENGTH atom_expr ) | -> atom_expr | EOF -> atom_expr ) )
			// Dafny.g:236:3: atom_expr ( '[' expression ']' -> ^( ARRAY_ACCESS atom_expr expression ) | '.' LENGTH -> ^( LENGTH atom_expr ) | -> atom_expr | EOF -> atom_expr )
			{
			pushFollow(FOLLOW_atom_expr_in_postfix_expr1536);
			atom_expr144=atom_expr();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) stream_atom_expr.add(atom_expr144.getTree());
			// Dafny.g:237:3: ( '[' expression ']' -> ^( ARRAY_ACCESS atom_expr expression ) | '.' LENGTH -> ^( LENGTH atom_expr ) | -> atom_expr | EOF -> atom_expr )
			int alt38=4;
			switch ( input.LA(1) ) {
			case 62:
				{
				alt38=1;
				}
				break;
			case DOT:
				{
				alt38=2;
				}
				break;
			case AND:
			case ASSERT:
			case ASSUME:
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
			case VAR:
			case WHILE:
			case 58:
			case 59:
			case 61:
			case 63:
				{
				alt38=3;
				}
				break;
			case EOF:
				{
				alt38=4;
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
					// Dafny.g:237:5: '[' expression ']'
					{
					char_literal145=(Token)match(input,62,FOLLOW_62_in_postfix_expr1542); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_62.add(char_literal145);

					pushFollow(FOLLOW_expression_in_postfix_expr1544);
					expression146=expression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_expression.add(expression146.getTree());
					char_literal147=(Token)match(input,63,FOLLOW_63_in_postfix_expr1546); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_63.add(char_literal147);

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

					root_0 = (DafnyTree)adaptor.nil();
					// 237:24: -> ^( ARRAY_ACCESS atom_expr expression )
					{
						// Dafny.g:237:27: ^( ARRAY_ACCESS atom_expr expression )
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
					// Dafny.g:238:5: '.' LENGTH
					{
					char_literal148=(Token)match(input,DOT,FOLLOW_DOT_in_postfix_expr1564); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_DOT.add(char_literal148);

					LENGTH149=(Token)match(input,LENGTH,FOLLOW_LENGTH_in_postfix_expr1566); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_LENGTH.add(LENGTH149);

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
					// 238:16: -> ^( LENGTH atom_expr )
					{
						// Dafny.g:238:19: ^( LENGTH atom_expr )
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
					// Dafny.g:239:5: 
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
					// 239:5: -> atom_expr
					{
						adaptor.addChild(root_0, stream_atom_expr.nextTree());
					}


					retval.tree = root_0;
					}

					}
					break;
				case 4 :
					// Dafny.g:240:5: EOF
					{
					EOF150=(Token)match(input,EOF,FOLLOW_EOF_in_postfix_expr1590); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_EOF.add(EOF150);

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
					// 240:9: -> atom_expr
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
	// Dafny.g:244:1: atom_expr : ( ID | LIT | quantifier | '(' ! expression ')' !| '{' ( expressions )? '}' -> ^( SETEX ( expressions )? ) | '[' ( expressions )? ']' -> ^( LISTEX ( expressions )? ) );
	public final DafnyParser.atom_expr_return atom_expr() throws RecognitionException {
		DafnyParser.atom_expr_return retval = new DafnyParser.atom_expr_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		Token ID151=null;
		Token LIT152=null;
		Token char_literal154=null;
		Token char_literal156=null;
		Token char_literal157=null;
		Token char_literal159=null;
		Token char_literal160=null;
		Token char_literal162=null;
		ParserRuleReturnScope quantifier153 =null;
		ParserRuleReturnScope expression155 =null;
		ParserRuleReturnScope expressions158 =null;
		ParserRuleReturnScope expressions161 =null;

		DafnyTree ID151_tree=null;
		DafnyTree LIT152_tree=null;
		DafnyTree char_literal154_tree=null;
		DafnyTree char_literal156_tree=null;
		DafnyTree char_literal157_tree=null;
		DafnyTree char_literal159_tree=null;
		DafnyTree char_literal160_tree=null;
		DafnyTree char_literal162_tree=null;
		RewriteRuleTokenStream stream_62=new RewriteRuleTokenStream(adaptor,"token 62");
		RewriteRuleTokenStream stream_BLOCK_BEGIN=new RewriteRuleTokenStream(adaptor,"token BLOCK_BEGIN");
		RewriteRuleTokenStream stream_63=new RewriteRuleTokenStream(adaptor,"token 63");
		RewriteRuleTokenStream stream_BLOCK_END=new RewriteRuleTokenStream(adaptor,"token BLOCK_END");
		RewriteRuleSubtreeStream stream_expressions=new RewriteRuleSubtreeStream(adaptor,"rule expressions");

		try {
			// Dafny.g:244:10: ( ID | LIT | quantifier | '(' ! expression ')' !| '{' ( expressions )? '}' -> ^( SETEX ( expressions )? ) | '[' ( expressions )? ']' -> ^( LISTEX ( expressions )? ) )
			int alt41=6;
			switch ( input.LA(1) ) {
			case ID:
				{
				alt41=1;
				}
				break;
			case LIT:
				{
				alt41=2;
				}
				break;
			case 57:
				{
				int LA41_3 = input.LA(2);
				if ( (LA41_3==ALL||LA41_3==EX) ) {
					alt41=3;
				}
				else if ( (LA41_3==BLOCK_BEGIN||LA41_3==ID||LA41_3==LIT||LA41_3==MINUS||LA41_3==NOT||LA41_3==57||LA41_3==62) ) {
					alt41=4;
				}

				else {
					if (state.backtracking>0) {state.failed=true; return retval;}
					int nvaeMark = input.mark();
					try {
						input.consume();
						NoViableAltException nvae =
							new NoViableAltException("", 41, 3, input);
						throw nvae;
					} finally {
						input.rewind(nvaeMark);
					}
				}

				}
				break;
			case BLOCK_BEGIN:
				{
				alt41=5;
				}
				break;
			case 62:
				{
				alt41=6;
				}
				break;
			default:
				if (state.backtracking>0) {state.failed=true; return retval;}
				NoViableAltException nvae =
					new NoViableAltException("", 41, 0, input);
				throw nvae;
			}
			switch (alt41) {
				case 1 :
					// Dafny.g:245:5: ID
					{
					root_0 = (DafnyTree)adaptor.nil();


					ID151=(Token)match(input,ID,FOLLOW_ID_in_atom_expr1612); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					ID151_tree = (DafnyTree)adaptor.create(ID151);
					adaptor.addChild(root_0, ID151_tree);
					}

					}
					break;
				case 2 :
					// Dafny.g:246:5: LIT
					{
					root_0 = (DafnyTree)adaptor.nil();


					LIT152=(Token)match(input,LIT,FOLLOW_LIT_in_atom_expr1618); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					LIT152_tree = (DafnyTree)adaptor.create(LIT152);
					adaptor.addChild(root_0, LIT152_tree);
					}

					}
					break;
				case 3 :
					// Dafny.g:247:5: quantifier
					{
					root_0 = (DafnyTree)adaptor.nil();


					pushFollow(FOLLOW_quantifier_in_atom_expr1624);
					quantifier153=quantifier();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, quantifier153.getTree());

					}
					break;
				case 4 :
					// Dafny.g:248:5: '(' ! expression ')' !
					{
					root_0 = (DafnyTree)adaptor.nil();


					char_literal154=(Token)match(input,57,FOLLOW_57_in_atom_expr1630); if (state.failed) return retval;
					pushFollow(FOLLOW_expression_in_atom_expr1633);
					expression155=expression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, expression155.getTree());

					char_literal156=(Token)match(input,58,FOLLOW_58_in_atom_expr1635); if (state.failed) return retval;
					}
					break;
				case 5 :
					// Dafny.g:249:5: '{' ( expressions )? '}'
					{
					char_literal157=(Token)match(input,BLOCK_BEGIN,FOLLOW_BLOCK_BEGIN_in_atom_expr1642); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_BLOCK_BEGIN.add(char_literal157);

					// Dafny.g:249:9: ( expressions )?
					int alt39=2;
					int LA39_0 = input.LA(1);
					if ( (LA39_0==BLOCK_BEGIN||LA39_0==ID||LA39_0==LIT||LA39_0==MINUS||LA39_0==NOT||LA39_0==57||LA39_0==62) ) {
						alt39=1;
					}
					switch (alt39) {
						case 1 :
							// Dafny.g:249:9: expressions
							{
							pushFollow(FOLLOW_expressions_in_atom_expr1644);
							expressions158=expressions();
							state._fsp--;
							if (state.failed) return retval;
							if ( state.backtracking==0 ) stream_expressions.add(expressions158.getTree());
							}
							break;

					}

					char_literal159=(Token)match(input,BLOCK_END,FOLLOW_BLOCK_END_in_atom_expr1647); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_BLOCK_END.add(char_literal159);

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
					// 249:26: -> ^( SETEX ( expressions )? )
					{
						// Dafny.g:249:29: ^( SETEX ( expressions )? )
						{
						DafnyTree root_1 = (DafnyTree)adaptor.nil();
						root_1 = (DafnyTree)adaptor.becomeRoot((DafnyTree)adaptor.create(SETEX, "SETEX"), root_1);
						// Dafny.g:249:37: ( expressions )?
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
					// Dafny.g:250:5: '[' ( expressions )? ']'
					{
					char_literal160=(Token)match(input,62,FOLLOW_62_in_atom_expr1662); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_62.add(char_literal160);

					// Dafny.g:250:9: ( expressions )?
					int alt40=2;
					int LA40_0 = input.LA(1);
					if ( (LA40_0==BLOCK_BEGIN||LA40_0==ID||LA40_0==LIT||LA40_0==MINUS||LA40_0==NOT||LA40_0==57||LA40_0==62) ) {
						alt40=1;
					}
					switch (alt40) {
						case 1 :
							// Dafny.g:250:9: expressions
							{
							pushFollow(FOLLOW_expressions_in_atom_expr1664);
							expressions161=expressions();
							state._fsp--;
							if (state.failed) return retval;
							if ( state.backtracking==0 ) stream_expressions.add(expressions161.getTree());
							}
							break;

					}

					char_literal162=(Token)match(input,63,FOLLOW_63_in_atom_expr1667); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_63.add(char_literal162);

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
					// 250:26: -> ^( LISTEX ( expressions )? )
					{
						// Dafny.g:250:29: ^( LISTEX ( expressions )? )
						{
						DafnyTree root_1 = (DafnyTree)adaptor.nil();
						root_1 = (DafnyTree)adaptor.becomeRoot((DafnyTree)adaptor.create(LISTEX, "LISTEX"), root_1);
						// Dafny.g:250:38: ( expressions )?
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
	// Dafny.g:253:1: quantifier : '(' ! ( ALL ^| EX ^) ID ':' ! type '::' ! expression ')' !;
	public final DafnyParser.quantifier_return quantifier() throws RecognitionException {
		DafnyParser.quantifier_return retval = new DafnyParser.quantifier_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		Token char_literal163=null;
		Token ALL164=null;
		Token EX165=null;
		Token ID166=null;
		Token char_literal167=null;
		Token string_literal169=null;
		Token char_literal171=null;
		ParserRuleReturnScope type168 =null;
		ParserRuleReturnScope expression170 =null;

		DafnyTree char_literal163_tree=null;
		DafnyTree ALL164_tree=null;
		DafnyTree EX165_tree=null;
		DafnyTree ID166_tree=null;
		DafnyTree char_literal167_tree=null;
		DafnyTree string_literal169_tree=null;
		DafnyTree char_literal171_tree=null;

		try {
			// Dafny.g:253:11: ( '(' ! ( ALL ^| EX ^) ID ':' ! type '::' ! expression ')' !)
			// Dafny.g:254:3: '(' ! ( ALL ^| EX ^) ID ':' ! type '::' ! expression ')' !
			{
			root_0 = (DafnyTree)adaptor.nil();


			char_literal163=(Token)match(input,57,FOLLOW_57_in_quantifier1688); if (state.failed) return retval;
			// Dafny.g:254:8: ( ALL ^| EX ^)
			int alt42=2;
			int LA42_0 = input.LA(1);
			if ( (LA42_0==ALL) ) {
				alt42=1;
			}
			else if ( (LA42_0==EX) ) {
				alt42=2;
			}

			else {
				if (state.backtracking>0) {state.failed=true; return retval;}
				NoViableAltException nvae =
					new NoViableAltException("", 42, 0, input);
				throw nvae;
			}

			switch (alt42) {
				case 1 :
					// Dafny.g:254:9: ALL ^
					{
					ALL164=(Token)match(input,ALL,FOLLOW_ALL_in_quantifier1692); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					ALL164_tree = (DafnyTree)adaptor.create(ALL164);
					root_0 = (DafnyTree)adaptor.becomeRoot(ALL164_tree, root_0);
					}

					}
					break;
				case 2 :
					// Dafny.g:254:16: EX ^
					{
					EX165=(Token)match(input,EX,FOLLOW_EX_in_quantifier1697); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					EX165_tree = (DafnyTree)adaptor.create(EX165);
					root_0 = (DafnyTree)adaptor.becomeRoot(EX165_tree, root_0);
					}

					}
					break;

			}

			ID166=(Token)match(input,ID,FOLLOW_ID_in_quantifier1701); if (state.failed) return retval;
			if ( state.backtracking==0 ) {
			ID166_tree = (DafnyTree)adaptor.create(ID166);
			adaptor.addChild(root_0, ID166_tree);
			}

			char_literal167=(Token)match(input,60,FOLLOW_60_in_quantifier1703); if (state.failed) return retval;
			pushFollow(FOLLOW_type_in_quantifier1706);
			type168=type();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, type168.getTree());

			string_literal169=(Token)match(input,DOUBLECOLON,FOLLOW_DOUBLECOLON_in_quantifier1708); if (state.failed) return retval;
			pushFollow(FOLLOW_expression_in_quantifier1711);
			expression170=expression();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, expression170.getTree());

			char_literal171=(Token)match(input,58,FOLLOW_58_in_quantifier1713); if (state.failed) return retval;
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
		// Dafny.g:185:5: ( ID ':=' 'call' )
		// Dafny.g:185:6: ID ':=' 'call'
		{
		match(input,ID,FOLLOW_ID_in_synpred1_Dafny1036); if (state.failed) return;

		match(input,ASSIGN,FOLLOW_ASSIGN_in_synpred1_Dafny1038); if (state.failed) return;

		match(input,CALL,FOLLOW_CALL_in_synpred1_Dafny1040); if (state.failed) return;

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



	public static final BitSet FOLLOW_LABEL_in_label535 = new BitSet(new long[]{0x0000000004000000L});
	public static final BitSet FOLLOW_ID_in_label538 = new BitSet(new long[]{0x1000000000000000L});
	public static final BitSet FOLLOW_60_in_label540 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_method_in_program554 = new BitSet(new long[]{0x0000008400800002L});
	public static final BitSet FOLLOW_function_in_program558 = new BitSet(new long[]{0x0000008400800002L});
	public static final BitSet FOLLOW_METHOD_in_method577 = new BitSet(new long[]{0x0000000004000000L});
	public static final BitSet FOLLOW_LEMMA_in_method581 = new BitSet(new long[]{0x0000000004000000L});
	public static final BitSet FOLLOW_ID_in_method586 = new BitSet(new long[]{0x0200000000000000L});
	public static final BitSet FOLLOW_57_in_method588 = new BitSet(new long[]{0x0400000004000000L});
	public static final BitSet FOLLOW_vars_in_method590 = new BitSet(new long[]{0x0400000000000000L});
	public static final BitSet FOLLOW_58_in_method593 = new BitSet(new long[]{0x0000A00000112000L});
	public static final BitSet FOLLOW_returns__in_method599 = new BitSet(new long[]{0x0000200000112000L});
	public static final BitSet FOLLOW_requires_in_method608 = new BitSet(new long[]{0x0000200000112000L});
	public static final BitSet FOLLOW_ensures_in_method617 = new BitSet(new long[]{0x0000000000112000L});
	public static final BitSet FOLLOW_decreases_in_method626 = new BitSet(new long[]{0x0000000000002000L});
	public static final BitSet FOLLOW_BLOCK_BEGIN_in_method633 = new BitSet(new long[]{0x00C000010C004A00L});
	public static final BitSet FOLLOW_statements_in_method635 = new BitSet(new long[]{0x0000000000004000L});
	public static final BitSet FOLLOW_BLOCK_END_in_method638 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_FUNCTION_in_function700 = new BitSet(new long[]{0x0000000004000000L});
	public static final BitSet FOLLOW_ID_in_function705 = new BitSet(new long[]{0x0200000000000000L});
	public static final BitSet FOLLOW_57_in_function707 = new BitSet(new long[]{0x0400000004000000L});
	public static final BitSet FOLLOW_vars_in_function710 = new BitSet(new long[]{0x0400000000000000L});
	public static final BitSet FOLLOW_58_in_function713 = new BitSet(new long[]{0x1000000000000000L});
	public static final BitSet FOLLOW_60_in_function716 = new BitSet(new long[]{0x0001000020000080L});
	public static final BitSet FOLLOW_type_in_function719 = new BitSet(new long[]{0x0000000000002000L});
	public static final BitSet FOLLOW_BLOCK_BEGIN_in_function723 = new BitSet(new long[]{0x4200052004002000L});
	public static final BitSet FOLLOW_expression_in_function726 = new BitSet(new long[]{0x0000000000004000L});
	public static final BitSet FOLLOW_BLOCK_END_in_function728 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_var_in_vars741 = new BitSet(new long[]{0x0800000000000002L});
	public static final BitSet FOLLOW_59_in_vars747 = new BitSet(new long[]{0x0000000004000000L});
	public static final BitSet FOLLOW_var_in_vars750 = new BitSet(new long[]{0x0800000000000002L});
	public static final BitSet FOLLOW_ID_in_var765 = new BitSet(new long[]{0x1000000000000000L});
	public static final BitSet FOLLOW_60_in_var767 = new BitSet(new long[]{0x0001000020000080L});
	public static final BitSet FOLLOW_type_in_var769 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_INT_in_type793 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_SET_in_type797 = new BitSet(new long[]{0x0000004000000000L});
	public static final BitSet FOLLOW_LT_in_type800 = new BitSet(new long[]{0x0000000020000000L});
	public static final BitSet FOLLOW_INT_in_type803 = new BitSet(new long[]{0x0000000002000000L});
	public static final BitSet FOLLOW_GT_in_type805 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_ARRAY_in_type812 = new BitSet(new long[]{0x0000004000000000L});
	public static final BitSet FOLLOW_LT_in_type815 = new BitSet(new long[]{0x0000000020000000L});
	public static final BitSet FOLLOW_INT_in_type818 = new BitSet(new long[]{0x0000000002000000L});
	public static final BitSet FOLLOW_GT_in_type820 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_RETURNS_in_returns_833 = new BitSet(new long[]{0x0200000000000000L});
	public static final BitSet FOLLOW_57_in_returns_836 = new BitSet(new long[]{0x0000000004000000L});
	public static final BitSet FOLLOW_vars_in_returns_839 = new BitSet(new long[]{0x0400000000000000L});
	public static final BitSet FOLLOW_58_in_returns_841 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_REQUIRES_in_requires854 = new BitSet(new long[]{0x4200052104002000L});
	public static final BitSet FOLLOW_label_in_requires857 = new BitSet(new long[]{0x4200052004002000L});
	public static final BitSet FOLLOW_expression_in_requires860 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_ENSURES_in_ensures872 = new BitSet(new long[]{0x4200052104002000L});
	public static final BitSet FOLLOW_label_in_ensures875 = new BitSet(new long[]{0x4200052004002000L});
	public static final BitSet FOLLOW_expression_in_ensures878 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_DECREASES_in_decreases890 = new BitSet(new long[]{0x4200052004002000L});
	public static final BitSet FOLLOW_expression_in_decreases893 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_INVARIANT_in_invariant905 = new BitSet(new long[]{0x4200052104002000L});
	public static final BitSet FOLLOW_label_in_invariant908 = new BitSet(new long[]{0x4200052004002000L});
	public static final BitSet FOLLOW_expression_in_invariant911 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_BLOCK_BEGIN_in_block923 = new BitSet(new long[]{0x00C000010C004A00L});
	public static final BitSet FOLLOW_statements_in_block925 = new BitSet(new long[]{0x0000000000004000L});
	public static final BitSet FOLLOW_BLOCK_END_in_block928 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_block_in_relaxedBlock951 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_statement_in_relaxedBlock957 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_statement_in_statements979 = new BitSet(new long[]{0x00C000010C000A02L});
	public static final BitSet FOLLOW_VAR_in_statement996 = new BitSet(new long[]{0x0000000004000000L});
	public static final BitSet FOLLOW_ID_in_statement999 = new BitSet(new long[]{0x1000000000000000L});
	public static final BitSet FOLLOW_60_in_statement1001 = new BitSet(new long[]{0x0001000020000080L});
	public static final BitSet FOLLOW_type_in_statement1004 = new BitSet(new long[]{0x2000000000000400L});
	public static final BitSet FOLLOW_ASSIGN_in_statement1007 = new BitSet(new long[]{0x4200052004002000L});
	public static final BitSet FOLLOW_expression_in_statement1010 = new BitSet(new long[]{0x2000000000000000L});
	public static final BitSet FOLLOW_61_in_statement1014 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_ID_in_statement1021 = new BitSet(new long[]{0x0000000000000400L});
	public static final BitSet FOLLOW_ASSIGN_in_statement1023 = new BitSet(new long[]{0x4200052004002000L});
	public static final BitSet FOLLOW_expression_in_statement1026 = new BitSet(new long[]{0x2000000000000000L});
	public static final BitSet FOLLOW_61_in_statement1028 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_ID_in_statement1047 = new BitSet(new long[]{0x0000000000000400L});
	public static final BitSet FOLLOW_ASSIGN_in_statement1049 = new BitSet(new long[]{0x0000000000008000L});
	public static final BitSet FOLLOW_CALL_in_statement1051 = new BitSet(new long[]{0x0000000004000000L});
	public static final BitSet FOLLOW_ID_in_statement1055 = new BitSet(new long[]{0x0200000000000000L});
	public static final BitSet FOLLOW_57_in_statement1057 = new BitSet(new long[]{0x4600052004002000L});
	public static final BitSet FOLLOW_expressions_in_statement1059 = new BitSet(new long[]{0x0400000000000000L});
	public static final BitSet FOLLOW_58_in_statement1062 = new BitSet(new long[]{0x2000000000000000L});
	public static final BitSet FOLLOW_61_in_statement1064 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_ids_in_statement1101 = new BitSet(new long[]{0x0000000000000400L});
	public static final BitSet FOLLOW_ASSIGN_in_statement1103 = new BitSet(new long[]{0x0000000000008000L});
	public static final BitSet FOLLOW_CALL_in_statement1105 = new BitSet(new long[]{0x0000000004000000L});
	public static final BitSet FOLLOW_ID_in_statement1107 = new BitSet(new long[]{0x0200000000000000L});
	public static final BitSet FOLLOW_57_in_statement1109 = new BitSet(new long[]{0x4600052004002000L});
	public static final BitSet FOLLOW_expressions_in_statement1111 = new BitSet(new long[]{0x0400000000000000L});
	public static final BitSet FOLLOW_58_in_statement1114 = new BitSet(new long[]{0x2000000000000000L});
	public static final BitSet FOLLOW_61_in_statement1116 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_label_in_statement1151 = new BitSet(new long[]{0x0080000000000000L});
	public static final BitSet FOLLOW_WHILE_in_statement1160 = new BitSet(new long[]{0x4200052004002000L});
	public static final BitSet FOLLOW_expression_in_statement1162 = new BitSet(new long[]{0x0000000080000000L});
	public static final BitSet FOLLOW_invariant_in_statement1164 = new BitSet(new long[]{0x0000000080010000L});
	public static final BitSet FOLLOW_decreases_in_statement1167 = new BitSet(new long[]{0x00C000010C002A00L});
	public static final BitSet FOLLOW_relaxedBlock_in_statement1169 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_label_in_statement1201 = new BitSet(new long[]{0x0000000008000000L});
	public static final BitSet FOLLOW_IF_in_statement1204 = new BitSet(new long[]{0x4200052004002000L});
	public static final BitSet FOLLOW_expression_in_statement1207 = new BitSet(new long[]{0x00C000010C002A00L});
	public static final BitSet FOLLOW_relaxedBlock_in_statement1209 = new BitSet(new long[]{0x0000000000080002L});
	public static final BitSet FOLLOW_ELSE_in_statement1230 = new BitSet(new long[]{0x00C000010C002A00L});
	public static final BitSet FOLLOW_relaxedBlock_in_statement1233 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_ASSERT_in_statement1242 = new BitSet(new long[]{0x4200052104002000L});
	public static final BitSet FOLLOW_LABEL_in_statement1247 = new BitSet(new long[]{0x0000000004000000L});
	public static final BitSet FOLLOW_ID_in_statement1250 = new BitSet(new long[]{0x1000000000000000L});
	public static final BitSet FOLLOW_60_in_statement1252 = new BitSet(new long[]{0x4200052004002000L});
	public static final BitSet FOLLOW_expression_in_statement1258 = new BitSet(new long[]{0x2000000000000000L});
	public static final BitSet FOLLOW_61_in_statement1260 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_ASSUME_in_statement1267 = new BitSet(new long[]{0x4200052104002000L});
	public static final BitSet FOLLOW_LABEL_in_statement1272 = new BitSet(new long[]{0x0000000004000000L});
	public static final BitSet FOLLOW_ID_in_statement1275 = new BitSet(new long[]{0x1000000000000000L});
	public static final BitSet FOLLOW_60_in_statement1277 = new BitSet(new long[]{0x4200052004002000L});
	public static final BitSet FOLLOW_expression_in_statement1283 = new BitSet(new long[]{0x2000000000000000L});
	public static final BitSet FOLLOW_61_in_statement1285 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_ID_in_ids1298 = new BitSet(new long[]{0x0800000000000000L});
	public static final BitSet FOLLOW_59_in_ids1301 = new BitSet(new long[]{0x0000000004000000L});
	public static final BitSet FOLLOW_ID_in_ids1304 = new BitSet(new long[]{0x0800000000000002L});
	public static final BitSet FOLLOW_expression_in_expressions1318 = new BitSet(new long[]{0x0800000000000002L});
	public static final BitSet FOLLOW_59_in_expressions1322 = new BitSet(new long[]{0x4200052004002000L});
	public static final BitSet FOLLOW_expression_in_expressions1325 = new BitSet(new long[]{0x0800000000000002L});
	public static final BitSet FOLLOW_or_expr_in_expression1340 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_and_expr_in_or_expr1349 = new BitSet(new long[]{0x0000080010000002L});
	public static final BitSet FOLLOW_OR_in_or_expr1354 = new BitSet(new long[]{0x4200052004002000L});
	public static final BitSet FOLLOW_IMPLIES_in_or_expr1359 = new BitSet(new long[]{0x4200052004002000L});
	public static final BitSet FOLLOW_or_expr_in_or_expr1363 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_rel_expr_in_and_expr1378 = new BitSet(new long[]{0x0000000000000022L});
	public static final BitSet FOLLOW_AND_in_and_expr1382 = new BitSet(new long[]{0x4200052004002000L});
	public static final BitSet FOLLOW_and_expr_in_and_expr1385 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_add_expr_in_rel_expr1400 = new BitSet(new long[]{0x0000004203200002L});
	public static final BitSet FOLLOW_LT_in_rel_expr1405 = new BitSet(new long[]{0x4200052004002000L});
	public static final BitSet FOLLOW_GT_in_rel_expr1410 = new BitSet(new long[]{0x4200052004002000L});
	public static final BitSet FOLLOW_EQ_in_rel_expr1415 = new BitSet(new long[]{0x4200052004002000L});
	public static final BitSet FOLLOW_LE_in_rel_expr1420 = new BitSet(new long[]{0x4200052004002000L});
	public static final BitSet FOLLOW_GE_in_rel_expr1425 = new BitSet(new long[]{0x4200052004002000L});
	public static final BitSet FOLLOW_add_expr_in_rel_expr1429 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_mul_expr_in_add_expr1444 = new BitSet(new long[]{0x0020110000000002L});
	public static final BitSet FOLLOW_set_in_add_expr1448 = new BitSet(new long[]{0x4200052004002000L});
	public static final BitSet FOLLOW_add_expr_in_add_expr1461 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_prefix_expr_in_mul_expr1476 = new BitSet(new long[]{0x0010000040000002L});
	public static final BitSet FOLLOW_set_in_mul_expr1480 = new BitSet(new long[]{0x4200052004002000L});
	public static final BitSet FOLLOW_mul_expr_in_mul_expr1489 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_MINUS_in_prefix_expr1506 = new BitSet(new long[]{0x4200052004002000L});
	public static final BitSet FOLLOW_prefix_expr_in_prefix_expr1509 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_NOT_in_prefix_expr1515 = new BitSet(new long[]{0x4200052004002000L});
	public static final BitSet FOLLOW_prefix_expr_in_prefix_expr1518 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_postfix_expr_in_prefix_expr1524 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_atom_expr_in_postfix_expr1536 = new BitSet(new long[]{0x4000000000020002L});
	public static final BitSet FOLLOW_62_in_postfix_expr1542 = new BitSet(new long[]{0x4200052004002000L});
	public static final BitSet FOLLOW_expression_in_postfix_expr1544 = new BitSet(new long[]{0x8000000000000000L});
	public static final BitSet FOLLOW_63_in_postfix_expr1546 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_DOT_in_postfix_expr1564 = new BitSet(new long[]{0x0000000800000000L});
	public static final BitSet FOLLOW_LENGTH_in_postfix_expr1566 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_EOF_in_postfix_expr1590 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_ID_in_atom_expr1612 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_LIT_in_atom_expr1618 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_quantifier_in_atom_expr1624 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_57_in_atom_expr1630 = new BitSet(new long[]{0x4200052004002000L});
	public static final BitSet FOLLOW_expression_in_atom_expr1633 = new BitSet(new long[]{0x0400000000000000L});
	public static final BitSet FOLLOW_58_in_atom_expr1635 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_BLOCK_BEGIN_in_atom_expr1642 = new BitSet(new long[]{0x4200052004006000L});
	public static final BitSet FOLLOW_expressions_in_atom_expr1644 = new BitSet(new long[]{0x0000000000004000L});
	public static final BitSet FOLLOW_BLOCK_END_in_atom_expr1647 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_62_in_atom_expr1662 = new BitSet(new long[]{0xC200052004002000L});
	public static final BitSet FOLLOW_expressions_in_atom_expr1664 = new BitSet(new long[]{0x8000000000000000L});
	public static final BitSet FOLLOW_63_in_atom_expr1667 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_57_in_quantifier1688 = new BitSet(new long[]{0x0000000000400010L});
	public static final BitSet FOLLOW_ALL_in_quantifier1692 = new BitSet(new long[]{0x0000000004000000L});
	public static final BitSet FOLLOW_EX_in_quantifier1697 = new BitSet(new long[]{0x0000000004000000L});
	public static final BitSet FOLLOW_ID_in_quantifier1701 = new BitSet(new long[]{0x1000000000000000L});
	public static final BitSet FOLLOW_60_in_quantifier1703 = new BitSet(new long[]{0x0001000020000080L});
	public static final BitSet FOLLOW_type_in_quantifier1706 = new BitSet(new long[]{0x0000000000040000L});
	public static final BitSet FOLLOW_DOUBLECOLON_in_quantifier1708 = new BitSet(new long[]{0x4200052004002000L});
	public static final BitSet FOLLOW_expression_in_quantifier1711 = new BitSet(new long[]{0x0400000000000000L});
	public static final BitSet FOLLOW_58_in_quantifier1713 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_ID_in_synpred1_Dafny1036 = new BitSet(new long[]{0x0000000000000400L});
	public static final BitSet FOLLOW_ASSIGN_in_synpred1_Dafny1038 = new BitSet(new long[]{0x0000000000008000L});
	public static final BitSet FOLLOW_CALL_in_synpred1_Dafny1040 = new BitSet(new long[]{0x0000000000000002L});
}
