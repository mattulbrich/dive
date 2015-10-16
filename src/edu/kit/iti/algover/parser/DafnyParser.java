// $ANTLR 3.5.1 Dafny.g 2015-10-16 14:01:23

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
		"FUNCTION", "GE", "GT", "ID", "IF", "IMPLIES", "INT", "INTERSECT", "INVARIANT", 
		"LABEL", "LE", "LEMMA", "LENGTH", "LISTEX", "LIT", "LT", "METHOD", "MINUS", 
		"MULTILINE_COMMENT", "NOT", "OR", "PLUS", "REQUIRES", "RESULTS", "RETURNS", 
		"SET", "SETEX", "SINGLELINE_COMMENT", "THEN", "TIMES", "UNION", "VAR", 
		"WHILE", "WS", "'('", "')'", "','", "':'", "';'", "'['", "']'"
	};
	public static final int EOF=-1;
	public static final int T__56=56;
	public static final int T__57=57;
	public static final int T__58=58;
	public static final int T__59=59;
	public static final int T__60=60;
	public static final int T__61=61;
	public static final int T__62=62;
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
	public static final int FUNCTION=22;
	public static final int GE=23;
	public static final int GT=24;
	public static final int ID=25;
	public static final int IF=26;
	public static final int IMPLIES=27;
	public static final int INT=28;
	public static final int INTERSECT=29;
	public static final int INVARIANT=30;
	public static final int LABEL=31;
	public static final int LE=32;
	public static final int LEMMA=33;
	public static final int LENGTH=34;
	public static final int LISTEX=35;
	public static final int LIT=36;
	public static final int LT=37;
	public static final int METHOD=38;
	public static final int MINUS=39;
	public static final int MULTILINE_COMMENT=40;
	public static final int NOT=41;
	public static final int OR=42;
	public static final int PLUS=43;
	public static final int REQUIRES=44;
	public static final int RESULTS=45;
	public static final int RETURNS=46;
	public static final int SET=47;
	public static final int SETEX=48;
	public static final int SINGLELINE_COMMENT=49;
	public static final int THEN=50;
	public static final int TIMES=51;
	public static final int UNION=52;
	public static final int VAR=53;
	public static final int WHILE=54;
	public static final int WS=55;

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
	// Dafny.g:107:1: label : 'label' ^ ID ':' !;
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
			// Dafny.g:107:6: ( 'label' ^ ID ':' !)
			// Dafny.g:108:3: 'label' ^ ID ':' !
			{
			root_0 = (DafnyTree)adaptor.nil();


			string_literal1=(Token)match(input,LABEL,FOLLOW_LABEL_in_label529); if (state.failed) return retval;
			if ( state.backtracking==0 ) {
			string_literal1_tree = (DafnyTree)adaptor.create(string_literal1);
			root_0 = (DafnyTree)adaptor.becomeRoot(string_literal1_tree, root_0);
			}

			ID2=(Token)match(input,ID,FOLLOW_ID_in_label532); if (state.failed) return retval;
			if ( state.backtracking==0 ) {
			ID2_tree = (DafnyTree)adaptor.create(ID2);
			adaptor.addChild(root_0, ID2_tree);
			}

			char_literal3=(Token)match(input,59,FOLLOW_59_in_label534); if (state.failed) return retval;
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
	// Dafny.g:111:1: program : ( method | function )+ ;
	public final DafnyParser.program_return program() throws RecognitionException {
		DafnyParser.program_return retval = new DafnyParser.program_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		ParserRuleReturnScope method4 =null;
		ParserRuleReturnScope function5 =null;


		try {
			// Dafny.g:111:8: ( ( method | function )+ )
			// Dafny.g:112:3: ( method | function )+
			{
			root_0 = (DafnyTree)adaptor.nil();


			// Dafny.g:112:3: ( method | function )+
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
					// Dafny.g:112:4: method
					{
					pushFollow(FOLLOW_method_in_program548);
					method4=method();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, method4.getTree());

					}
					break;
				case 2 :
					// Dafny.g:112:13: function
					{
					pushFollow(FOLLOW_function_in_program552);
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
	// Dafny.g:115:1: method : tok= ( 'method' | 'lemma' ) ID '(' ( vars )? ')' ( returns_ )? ( requires )* ( ensures )* ( decreases )? '{' ( statements )? '}' -> ^( METHOD[tok] ID ^( ARGS ( vars )? ) ( returns_ )? ( requires )* ( ensures )* ( decreases )? ^( BLOCK ( statements )? ) ) ;
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
		RewriteRuleTokenStream stream_57=new RewriteRuleTokenStream(adaptor,"token 57");
		RewriteRuleTokenStream stream_56=new RewriteRuleTokenStream(adaptor,"token 56");
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
			// Dafny.g:115:7: (tok= ( 'method' | 'lemma' ) ID '(' ( vars )? ')' ( returns_ )? ( requires )* ( ensures )* ( decreases )? '{' ( statements )? '}' -> ^( METHOD[tok] ID ^( ARGS ( vars )? ) ( returns_ )? ( requires )* ( ensures )* ( decreases )? ^( BLOCK ( statements )? ) ) )
			// Dafny.g:116:3: tok= ( 'method' | 'lemma' ) ID '(' ( vars )? ')' ( returns_ )? ( requires )* ( ensures )* ( decreases )? '{' ( statements )? '}'
			{
			// Dafny.g:116:9: ( 'method' | 'lemma' )
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
					// Dafny.g:116:10: 'method'
					{
					tok=(Token)match(input,METHOD,FOLLOW_METHOD_in_method571); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_METHOD.add(tok);

					}
					break;
				case 2 :
					// Dafny.g:116:21: 'lemma'
					{
					tok=(Token)match(input,LEMMA,FOLLOW_LEMMA_in_method575); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_LEMMA.add(tok);

					}
					break;

			}

			ID6=(Token)match(input,ID,FOLLOW_ID_in_method580); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_ID.add(ID6);

			char_literal7=(Token)match(input,56,FOLLOW_56_in_method582); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_56.add(char_literal7);

			// Dafny.g:117:10: ( vars )?
			int alt3=2;
			int LA3_0 = input.LA(1);
			if ( (LA3_0==ID) ) {
				alt3=1;
			}
			switch (alt3) {
				case 1 :
					// Dafny.g:117:10: vars
					{
					pushFollow(FOLLOW_vars_in_method584);
					vars8=vars();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_vars.add(vars8.getTree());
					}
					break;

			}

			char_literal9=(Token)match(input,57,FOLLOW_57_in_method587); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_57.add(char_literal9);

			// Dafny.g:118:3: ( returns_ )?
			int alt4=2;
			int LA4_0 = input.LA(1);
			if ( (LA4_0==RETURNS) ) {
				alt4=1;
			}
			switch (alt4) {
				case 1 :
					// Dafny.g:118:5: returns_
					{
					pushFollow(FOLLOW_returns__in_method593);
					returns_10=returns_();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_returns_.add(returns_10.getTree());
					}
					break;

			}

			// Dafny.g:119:3: ( requires )*
			loop5:
			while (true) {
				int alt5=2;
				int LA5_0 = input.LA(1);
				if ( (LA5_0==REQUIRES) ) {
					alt5=1;
				}

				switch (alt5) {
				case 1 :
					// Dafny.g:119:5: requires
					{
					pushFollow(FOLLOW_requires_in_method602);
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

			// Dafny.g:120:3: ( ensures )*
			loop6:
			while (true) {
				int alt6=2;
				int LA6_0 = input.LA(1);
				if ( (LA6_0==ENSURES) ) {
					alt6=1;
				}

				switch (alt6) {
				case 1 :
					// Dafny.g:120:5: ensures
					{
					pushFollow(FOLLOW_ensures_in_method611);
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

			// Dafny.g:121:3: ( decreases )?
			int alt7=2;
			int LA7_0 = input.LA(1);
			if ( (LA7_0==DECREASES) ) {
				alt7=1;
			}
			switch (alt7) {
				case 1 :
					// Dafny.g:121:5: decreases
					{
					pushFollow(FOLLOW_decreases_in_method620);
					decreases13=decreases();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_decreases.add(decreases13.getTree());
					}
					break;

			}

			char_literal14=(Token)match(input,BLOCK_BEGIN,FOLLOW_BLOCK_BEGIN_in_method627); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_BLOCK_BEGIN.add(char_literal14);

			// Dafny.g:122:7: ( statements )?
			int alt8=2;
			int LA8_0 = input.LA(1);
			if ( (LA8_0==ASSERT||(LA8_0 >= ID && LA8_0 <= IF)||LA8_0==LABEL||(LA8_0 >= VAR && LA8_0 <= WHILE)) ) {
				alt8=1;
			}
			switch (alt8) {
				case 1 :
					// Dafny.g:122:7: statements
					{
					pushFollow(FOLLOW_statements_in_method629);
					statements15=statements();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_statements.add(statements15.getTree());
					}
					break;

			}

			char_literal16=(Token)match(input,BLOCK_END,FOLLOW_BLOCK_END_in_method632); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_BLOCK_END.add(char_literal16);

			// AST REWRITE
			// elements: returns_, decreases, vars, ID, statements, requires, ensures
			// token labels: 
			// rule labels: retval
			// token list labels: 
			// rule list labels: 
			// wildcard labels: 
			if ( state.backtracking==0 ) {
			retval.tree = root_0;
			RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

			root_0 = (DafnyTree)adaptor.nil();
			// 123:3: -> ^( METHOD[tok] ID ^( ARGS ( vars )? ) ( returns_ )? ( requires )* ( ensures )* ( decreases )? ^( BLOCK ( statements )? ) )
			{
				// Dafny.g:124:5: ^( METHOD[tok] ID ^( ARGS ( vars )? ) ( returns_ )? ( requires )* ( ensures )* ( decreases )? ^( BLOCK ( statements )? ) )
				{
				DafnyTree root_1 = (DafnyTree)adaptor.nil();
				root_1 = (DafnyTree)adaptor.becomeRoot((DafnyTree)adaptor.create(METHOD, tok), root_1);
				adaptor.addChild(root_1, stream_ID.nextNode());
				// Dafny.g:124:22: ^( ARGS ( vars )? )
				{
				DafnyTree root_2 = (DafnyTree)adaptor.nil();
				root_2 = (DafnyTree)adaptor.becomeRoot((DafnyTree)adaptor.create(ARGS, "ARGS"), root_2);
				// Dafny.g:124:29: ( vars )?
				if ( stream_vars.hasNext() ) {
					adaptor.addChild(root_2, stream_vars.nextTree());
				}
				stream_vars.reset();

				adaptor.addChild(root_1, root_2);
				}

				// Dafny.g:124:36: ( returns_ )?
				if ( stream_returns_.hasNext() ) {
					adaptor.addChild(root_1, stream_returns_.nextTree());
				}
				stream_returns_.reset();

				// Dafny.g:124:46: ( requires )*
				while ( stream_requires.hasNext() ) {
					adaptor.addChild(root_1, stream_requires.nextTree());
				}
				stream_requires.reset();

				// Dafny.g:124:56: ( ensures )*
				while ( stream_ensures.hasNext() ) {
					adaptor.addChild(root_1, stream_ensures.nextTree());
				}
				stream_ensures.reset();

				// Dafny.g:125:9: ( decreases )?
				if ( stream_decreases.hasNext() ) {
					adaptor.addChild(root_1, stream_decreases.nextTree());
				}
				stream_decreases.reset();

				// Dafny.g:125:20: ^( BLOCK ( statements )? )
				{
				DafnyTree root_2 = (DafnyTree)adaptor.nil();
				root_2 = (DafnyTree)adaptor.becomeRoot((DafnyTree)adaptor.create(BLOCK, "BLOCK"), root_2);
				// Dafny.g:125:28: ( statements )?
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
	// Dafny.g:128:1: function : 'function' ^ ID '(' ! ( vars )? ')' ! ':' ! type '{' ! expression '}' !;
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
			// Dafny.g:128:9: ( 'function' ^ ID '(' ! ( vars )? ')' ! ':' ! type '{' ! expression '}' !)
			// Dafny.g:129:3: 'function' ^ ID '(' ! ( vars )? ')' ! ':' ! type '{' ! expression '}' !
			{
			root_0 = (DafnyTree)adaptor.nil();


			string_literal17=(Token)match(input,FUNCTION,FOLLOW_FUNCTION_in_function694); if (state.failed) return retval;
			if ( state.backtracking==0 ) {
			string_literal17_tree = (DafnyTree)adaptor.create(string_literal17);
			root_0 = (DafnyTree)adaptor.becomeRoot(string_literal17_tree, root_0);
			}

			ID18=(Token)match(input,ID,FOLLOW_ID_in_function699); if (state.failed) return retval;
			if ( state.backtracking==0 ) {
			ID18_tree = (DafnyTree)adaptor.create(ID18);
			adaptor.addChild(root_0, ID18_tree);
			}

			char_literal19=(Token)match(input,56,FOLLOW_56_in_function701); if (state.failed) return retval;
			// Dafny.g:130:11: ( vars )?
			int alt9=2;
			int LA9_0 = input.LA(1);
			if ( (LA9_0==ID) ) {
				alt9=1;
			}
			switch (alt9) {
				case 1 :
					// Dafny.g:130:11: vars
					{
					pushFollow(FOLLOW_vars_in_function704);
					vars20=vars();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, vars20.getTree());

					}
					break;

			}

			char_literal21=(Token)match(input,57,FOLLOW_57_in_function707); if (state.failed) return retval;
			char_literal22=(Token)match(input,59,FOLLOW_59_in_function710); if (state.failed) return retval;
			pushFollow(FOLLOW_type_in_function713);
			type23=type();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, type23.getTree());

			char_literal24=(Token)match(input,BLOCK_BEGIN,FOLLOW_BLOCK_BEGIN_in_function717); if (state.failed) return retval;
			pushFollow(FOLLOW_expression_in_function720);
			expression25=expression();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, expression25.getTree());

			char_literal26=(Token)match(input,BLOCK_END,FOLLOW_BLOCK_END_in_function722); if (state.failed) return retval;
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
	// Dafny.g:134:1: vars : var ( ',' ! var )* ;
	public final DafnyParser.vars_return vars() throws RecognitionException {
		DafnyParser.vars_return retval = new DafnyParser.vars_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		Token char_literal28=null;
		ParserRuleReturnScope var27 =null;
		ParserRuleReturnScope var29 =null;

		DafnyTree char_literal28_tree=null;

		try {
			// Dafny.g:134:5: ( var ( ',' ! var )* )
			// Dafny.g:135:3: var ( ',' ! var )*
			{
			root_0 = (DafnyTree)adaptor.nil();


			pushFollow(FOLLOW_var_in_vars735);
			var27=var();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, var27.getTree());

			// Dafny.g:136:3: ( ',' ! var )*
			loop10:
			while (true) {
				int alt10=2;
				int LA10_0 = input.LA(1);
				if ( (LA10_0==58) ) {
					alt10=1;
				}

				switch (alt10) {
				case 1 :
					// Dafny.g:136:5: ',' ! var
					{
					char_literal28=(Token)match(input,58,FOLLOW_58_in_vars741); if (state.failed) return retval;
					pushFollow(FOLLOW_var_in_vars744);
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
	// Dafny.g:139:1: var : ID ':' type -> ^( VAR ID type ) ;
	public final DafnyParser.var_return var() throws RecognitionException {
		DafnyParser.var_return retval = new DafnyParser.var_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		Token ID30=null;
		Token char_literal31=null;
		ParserRuleReturnScope type32 =null;

		DafnyTree ID30_tree=null;
		DafnyTree char_literal31_tree=null;
		RewriteRuleTokenStream stream_59=new RewriteRuleTokenStream(adaptor,"token 59");
		RewriteRuleTokenStream stream_ID=new RewriteRuleTokenStream(adaptor,"token ID");
		RewriteRuleSubtreeStream stream_type=new RewriteRuleSubtreeStream(adaptor,"rule type");

		try {
			// Dafny.g:139:4: ( ID ':' type -> ^( VAR ID type ) )
			// Dafny.g:140:3: ID ':' type
			{
			ID30=(Token)match(input,ID,FOLLOW_ID_in_var759); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_ID.add(ID30);

			char_literal31=(Token)match(input,59,FOLLOW_59_in_var761); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_59.add(char_literal31);

			pushFollow(FOLLOW_type_in_var763);
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
			// 140:15: -> ^( VAR ID type )
			{
				// Dafny.g:140:18: ^( VAR ID type )
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
	// Dafny.g:143:1: type : ( INT | SET ^ '<' ! INT '>' !| ARRAY ^ '<' ! INT '>' !);
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
			// Dafny.g:143:5: ( INT | SET ^ '<' ! INT '>' !| ARRAY ^ '<' ! INT '>' !)
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
					// Dafny.g:144:5: INT
					{
					root_0 = (DafnyTree)adaptor.nil();


					INT33=(Token)match(input,INT,FOLLOW_INT_in_type787); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					INT33_tree = (DafnyTree)adaptor.create(INT33);
					adaptor.addChild(root_0, INT33_tree);
					}

					}
					break;
				case 2 :
					// Dafny.g:144:11: SET ^ '<' ! INT '>' !
					{
					root_0 = (DafnyTree)adaptor.nil();


					SET34=(Token)match(input,SET,FOLLOW_SET_in_type791); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					SET34_tree = (DafnyTree)adaptor.create(SET34);
					root_0 = (DafnyTree)adaptor.becomeRoot(SET34_tree, root_0);
					}

					char_literal35=(Token)match(input,LT,FOLLOW_LT_in_type794); if (state.failed) return retval;
					INT36=(Token)match(input,INT,FOLLOW_INT_in_type797); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					INT36_tree = (DafnyTree)adaptor.create(INT36);
					adaptor.addChild(root_0, INT36_tree);
					}

					char_literal37=(Token)match(input,GT,FOLLOW_GT_in_type799); if (state.failed) return retval;
					}
					break;
				case 3 :
					// Dafny.g:145:5: ARRAY ^ '<' ! INT '>' !
					{
					root_0 = (DafnyTree)adaptor.nil();


					ARRAY38=(Token)match(input,ARRAY,FOLLOW_ARRAY_in_type806); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					ARRAY38_tree = (DafnyTree)adaptor.create(ARRAY38);
					root_0 = (DafnyTree)adaptor.becomeRoot(ARRAY38_tree, root_0);
					}

					char_literal39=(Token)match(input,LT,FOLLOW_LT_in_type809); if (state.failed) return retval;
					INT40=(Token)match(input,INT,FOLLOW_INT_in_type812); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					INT40_tree = (DafnyTree)adaptor.create(INT40);
					adaptor.addChild(root_0, INT40_tree);
					}

					char_literal41=(Token)match(input,GT,FOLLOW_GT_in_type814); if (state.failed) return retval;
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
	// Dafny.g:148:1: returns_ : RETURNS ^ '(' ! vars ')' !;
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
			// Dafny.g:148:9: ( RETURNS ^ '(' ! vars ')' !)
			// Dafny.g:149:3: RETURNS ^ '(' ! vars ')' !
			{
			root_0 = (DafnyTree)adaptor.nil();


			RETURNS42=(Token)match(input,RETURNS,FOLLOW_RETURNS_in_returns_827); if (state.failed) return retval;
			if ( state.backtracking==0 ) {
			RETURNS42_tree = (DafnyTree)adaptor.create(RETURNS42);
			root_0 = (DafnyTree)adaptor.becomeRoot(RETURNS42_tree, root_0);
			}

			char_literal43=(Token)match(input,56,FOLLOW_56_in_returns_830); if (state.failed) return retval;
			pushFollow(FOLLOW_vars_in_returns_833);
			vars44=vars();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, vars44.getTree());

			char_literal45=(Token)match(input,57,FOLLOW_57_in_returns_835); if (state.failed) return retval;
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
	// Dafny.g:152:1: requires : REQUIRES ^ ( label )? expression ;
	public final DafnyParser.requires_return requires() throws RecognitionException {
		DafnyParser.requires_return retval = new DafnyParser.requires_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		Token REQUIRES46=null;
		ParserRuleReturnScope label47 =null;
		ParserRuleReturnScope expression48 =null;

		DafnyTree REQUIRES46_tree=null;

		try {
			// Dafny.g:152:9: ( REQUIRES ^ ( label )? expression )
			// Dafny.g:153:3: REQUIRES ^ ( label )? expression
			{
			root_0 = (DafnyTree)adaptor.nil();


			REQUIRES46=(Token)match(input,REQUIRES,FOLLOW_REQUIRES_in_requires848); if (state.failed) return retval;
			if ( state.backtracking==0 ) {
			REQUIRES46_tree = (DafnyTree)adaptor.create(REQUIRES46);
			root_0 = (DafnyTree)adaptor.becomeRoot(REQUIRES46_tree, root_0);
			}

			// Dafny.g:153:13: ( label )?
			int alt12=2;
			int LA12_0 = input.LA(1);
			if ( (LA12_0==LABEL) ) {
				alt12=1;
			}
			switch (alt12) {
				case 1 :
					// Dafny.g:153:13: label
					{
					pushFollow(FOLLOW_label_in_requires851);
					label47=label();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, label47.getTree());

					}
					break;

			}

			pushFollow(FOLLOW_expression_in_requires854);
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
	// Dafny.g:156:1: ensures : ENSURES ^ ( label )? expression ;
	public final DafnyParser.ensures_return ensures() throws RecognitionException {
		DafnyParser.ensures_return retval = new DafnyParser.ensures_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		Token ENSURES49=null;
		ParserRuleReturnScope label50 =null;
		ParserRuleReturnScope expression51 =null;

		DafnyTree ENSURES49_tree=null;

		try {
			// Dafny.g:156:8: ( ENSURES ^ ( label )? expression )
			// Dafny.g:157:3: ENSURES ^ ( label )? expression
			{
			root_0 = (DafnyTree)adaptor.nil();


			ENSURES49=(Token)match(input,ENSURES,FOLLOW_ENSURES_in_ensures866); if (state.failed) return retval;
			if ( state.backtracking==0 ) {
			ENSURES49_tree = (DafnyTree)adaptor.create(ENSURES49);
			root_0 = (DafnyTree)adaptor.becomeRoot(ENSURES49_tree, root_0);
			}

			// Dafny.g:157:12: ( label )?
			int alt13=2;
			int LA13_0 = input.LA(1);
			if ( (LA13_0==LABEL) ) {
				alt13=1;
			}
			switch (alt13) {
				case 1 :
					// Dafny.g:157:12: label
					{
					pushFollow(FOLLOW_label_in_ensures869);
					label50=label();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, label50.getTree());

					}
					break;

			}

			pushFollow(FOLLOW_expression_in_ensures872);
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
	// Dafny.g:160:1: decreases : DECREASES ^ expression ;
	public final DafnyParser.decreases_return decreases() throws RecognitionException {
		DafnyParser.decreases_return retval = new DafnyParser.decreases_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		Token DECREASES52=null;
		ParserRuleReturnScope expression53 =null;

		DafnyTree DECREASES52_tree=null;

		try {
			// Dafny.g:160:10: ( DECREASES ^ expression )
			// Dafny.g:161:3: DECREASES ^ expression
			{
			root_0 = (DafnyTree)adaptor.nil();


			DECREASES52=(Token)match(input,DECREASES,FOLLOW_DECREASES_in_decreases884); if (state.failed) return retval;
			if ( state.backtracking==0 ) {
			DECREASES52_tree = (DafnyTree)adaptor.create(DECREASES52);
			root_0 = (DafnyTree)adaptor.becomeRoot(DECREASES52_tree, root_0);
			}

			pushFollow(FOLLOW_expression_in_decreases887);
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
	// Dafny.g:164:1: invariant : INVARIANT ^ ( label )? expression ;
	public final DafnyParser.invariant_return invariant() throws RecognitionException {
		DafnyParser.invariant_return retval = new DafnyParser.invariant_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		Token INVARIANT54=null;
		ParserRuleReturnScope label55 =null;
		ParserRuleReturnScope expression56 =null;

		DafnyTree INVARIANT54_tree=null;

		try {
			// Dafny.g:164:10: ( INVARIANT ^ ( label )? expression )
			// Dafny.g:165:3: INVARIANT ^ ( label )? expression
			{
			root_0 = (DafnyTree)adaptor.nil();


			INVARIANT54=(Token)match(input,INVARIANT,FOLLOW_INVARIANT_in_invariant899); if (state.failed) return retval;
			if ( state.backtracking==0 ) {
			INVARIANT54_tree = (DafnyTree)adaptor.create(INVARIANT54);
			root_0 = (DafnyTree)adaptor.becomeRoot(INVARIANT54_tree, root_0);
			}

			// Dafny.g:165:14: ( label )?
			int alt14=2;
			int LA14_0 = input.LA(1);
			if ( (LA14_0==LABEL) ) {
				alt14=1;
			}
			switch (alt14) {
				case 1 :
					// Dafny.g:165:14: label
					{
					pushFollow(FOLLOW_label_in_invariant902);
					label55=label();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, label55.getTree());

					}
					break;

			}

			pushFollow(FOLLOW_expression_in_invariant905);
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
	// Dafny.g:168:1: block : '{' ( statements )? '}' -> ^( BLOCK ( statements )? ) ;
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
			// Dafny.g:168:6: ( '{' ( statements )? '}' -> ^( BLOCK ( statements )? ) )
			// Dafny.g:169:3: '{' ( statements )? '}'
			{
			char_literal57=(Token)match(input,BLOCK_BEGIN,FOLLOW_BLOCK_BEGIN_in_block917); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_BLOCK_BEGIN.add(char_literal57);

			// Dafny.g:169:7: ( statements )?
			int alt15=2;
			int LA15_0 = input.LA(1);
			if ( (LA15_0==ASSERT||(LA15_0 >= ID && LA15_0 <= IF)||LA15_0==LABEL||(LA15_0 >= VAR && LA15_0 <= WHILE)) ) {
				alt15=1;
			}
			switch (alt15) {
				case 1 :
					// Dafny.g:169:7: statements
					{
					pushFollow(FOLLOW_statements_in_block919);
					statements58=statements();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_statements.add(statements58.getTree());
					}
					break;

			}

			char_literal59=(Token)match(input,BLOCK_END,FOLLOW_BLOCK_END_in_block922); if (state.failed) return retval; 
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
			// 169:23: -> ^( BLOCK ( statements )? )
			{
				// Dafny.g:169:26: ^( BLOCK ( statements )? )
				{
				DafnyTree root_1 = (DafnyTree)adaptor.nil();
				root_1 = (DafnyTree)adaptor.becomeRoot((DafnyTree)adaptor.create(BLOCK, "BLOCK"), root_1);
				// Dafny.g:169:34: ( statements )?
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
	// Dafny.g:172:1: relaxedBlock : ( block | statement -> ^( BLOCK statement ) );
	public final DafnyParser.relaxedBlock_return relaxedBlock() throws RecognitionException {
		DafnyParser.relaxedBlock_return retval = new DafnyParser.relaxedBlock_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		ParserRuleReturnScope block60 =null;
		ParserRuleReturnScope statement61 =null;

		RewriteRuleSubtreeStream stream_statement=new RewriteRuleSubtreeStream(adaptor,"rule statement");

		try {
			// Dafny.g:172:13: ( block | statement -> ^( BLOCK statement ) )
			int alt16=2;
			int LA16_0 = input.LA(1);
			if ( (LA16_0==BLOCK_BEGIN) ) {
				alt16=1;
			}
			else if ( (LA16_0==ASSERT||(LA16_0 >= ID && LA16_0 <= IF)||LA16_0==LABEL||(LA16_0 >= VAR && LA16_0 <= WHILE)) ) {
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
					// Dafny.g:173:5: block
					{
					root_0 = (DafnyTree)adaptor.nil();


					pushFollow(FOLLOW_block_in_relaxedBlock945);
					block60=block();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, block60.getTree());

					}
					break;
				case 2 :
					// Dafny.g:174:5: statement
					{
					pushFollow(FOLLOW_statement_in_relaxedBlock951);
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
					// 174:15: -> ^( BLOCK statement )
					{
						// Dafny.g:174:18: ^( BLOCK statement )
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
	// Dafny.g:177:1: statements : ( statement )+ ;
	public final DafnyParser.statements_return statements() throws RecognitionException {
		DafnyParser.statements_return retval = new DafnyParser.statements_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		ParserRuleReturnScope statement62 =null;


		try {
			// Dafny.g:177:11: ( ( statement )+ )
			// Dafny.g:178:3: ( statement )+
			{
			root_0 = (DafnyTree)adaptor.nil();


			// Dafny.g:178:3: ( statement )+
			int cnt17=0;
			loop17:
			while (true) {
				int alt17=2;
				int LA17_0 = input.LA(1);
				if ( (LA17_0==ASSERT||(LA17_0 >= ID && LA17_0 <= IF)||LA17_0==LABEL||(LA17_0 >= VAR && LA17_0 <= WHILE)) ) {
					alt17=1;
				}

				switch (alt17) {
				case 1 :
					// Dafny.g:178:5: statement
					{
					pushFollow(FOLLOW_statement_in_statements973);
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
	// Dafny.g:181:1: statement : ( VAR ^ ID ':' ! type ( ':=' ! expression )? ';' !| ID ':=' ^ expression ';' !| ( ID ':=' 'call' )=>r= ID ':=' 'call' f= ID '(' ( expressions )? ')' ';' -> ^( 'call' $f ^( RESULTS $r) ^( ARGS ( expressions )? ) ) | ids ':=' 'call' ID '(' ( expressions )? ')' ';' -> ^( 'call' ID ^( RESULTS ids ) ^( ARGS ( expressions )? ) ) | ( label )? 'while' expression ( invariant )+ decreases relaxedBlock -> ^( 'while' ( label )? expression ( invariant )+ decreases relaxedBlock ) | ( label )? 'if' ^ expression relaxedBlock ( options {greedy=true; } : 'else' ! relaxedBlock )? | 'assert' ^ ( 'label' ! ID ':' !)? expression ';' !);
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
		RewriteRuleTokenStream stream_CALL=new RewriteRuleTokenStream(adaptor,"token CALL");
		RewriteRuleTokenStream stream_57=new RewriteRuleTokenStream(adaptor,"token 57");
		RewriteRuleTokenStream stream_56=new RewriteRuleTokenStream(adaptor,"token 56");
		RewriteRuleTokenStream stream_WHILE=new RewriteRuleTokenStream(adaptor,"token WHILE");
		RewriteRuleTokenStream stream_ID=new RewriteRuleTokenStream(adaptor,"token ID");
		RewriteRuleTokenStream stream_60=new RewriteRuleTokenStream(adaptor,"token 60");
		RewriteRuleTokenStream stream_ASSIGN=new RewriteRuleTokenStream(adaptor,"token ASSIGN");
		RewriteRuleSubtreeStream stream_expression=new RewriteRuleSubtreeStream(adaptor,"rule expression");
		RewriteRuleSubtreeStream stream_invariant=new RewriteRuleSubtreeStream(adaptor,"rule invariant");
		RewriteRuleSubtreeStream stream_decreases=new RewriteRuleSubtreeStream(adaptor,"rule decreases");
		RewriteRuleSubtreeStream stream_ids=new RewriteRuleSubtreeStream(adaptor,"rule ids");
		RewriteRuleSubtreeStream stream_label=new RewriteRuleSubtreeStream(adaptor,"rule label");
		RewriteRuleSubtreeStream stream_relaxedBlock=new RewriteRuleSubtreeStream(adaptor,"rule relaxedBlock");
		RewriteRuleSubtreeStream stream_expressions=new RewriteRuleSubtreeStream(adaptor,"rule expressions");

		try {
			// Dafny.g:181:10: ( VAR ^ ID ':' ! type ( ':=' ! expression )? ';' !| ID ':=' ^ expression ';' !| ( ID ':=' 'call' )=>r= ID ':=' 'call' f= ID '(' ( expressions )? ')' ';' -> ^( 'call' $f ^( RESULTS $r) ^( ARGS ( expressions )? ) ) | ids ':=' 'call' ID '(' ( expressions )? ')' ';' -> ^( 'call' ID ^( RESULTS ids ) ^( ARGS ( expressions )? ) ) | ( label )? 'while' expression ( invariant )+ decreases relaxedBlock -> ^( 'while' ( label )? expression ( invariant )+ decreases relaxedBlock ) | ( label )? 'if' ^ expression relaxedBlock ( options {greedy=true; } : 'else' ! relaxedBlock )? | 'assert' ^ ( 'label' ! ID ':' !)? expression ';' !)
			int alt26=7;
			switch ( input.LA(1) ) {
			case VAR:
				{
				alt26=1;
				}
				break;
			case ID:
				{
				int LA26_2 = input.LA(2);
				if ( (LA26_2==ASSIGN) ) {
					int LA26_7 = input.LA(3);
					if ( (LA26_7==CALL) && (synpred1_Dafny())) {
						alt26=3;
					}
					else if ( (LA26_7==BLOCK_BEGIN||LA26_7==ID||LA26_7==LIT||LA26_7==MINUS||LA26_7==NOT||LA26_7==56||LA26_7==61) ) {
						alt26=2;
					}

					else {
						if (state.backtracking>0) {state.failed=true; return retval;}
						int nvaeMark = input.mark();
						try {
							for (int nvaeConsume = 0; nvaeConsume < 3 - 1; nvaeConsume++) {
								input.consume();
							}
							NoViableAltException nvae =
								new NoViableAltException("", 26, 7, input);
							throw nvae;
						} finally {
							input.rewind(nvaeMark);
						}
					}

				}
				else if ( (LA26_2==58) ) {
					alt26=4;
				}

				else {
					if (state.backtracking>0) {state.failed=true; return retval;}
					int nvaeMark = input.mark();
					try {
						input.consume();
						NoViableAltException nvae =
							new NoViableAltException("", 26, 2, input);
						throw nvae;
					} finally {
						input.rewind(nvaeMark);
					}
				}

				}
				break;
			case LABEL:
				{
				int LA26_3 = input.LA(2);
				if ( (LA26_3==ID) ) {
					int LA26_9 = input.LA(3);
					if ( (LA26_9==59) ) {
						int LA26_12 = input.LA(4);
						if ( (LA26_12==WHILE) ) {
							alt26=5;
						}
						else if ( (LA26_12==IF) ) {
							alt26=6;
						}

						else {
							if (state.backtracking>0) {state.failed=true; return retval;}
							int nvaeMark = input.mark();
							try {
								for (int nvaeConsume = 0; nvaeConsume < 4 - 1; nvaeConsume++) {
									input.consume();
								}
								NoViableAltException nvae =
									new NoViableAltException("", 26, 12, input);
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
								new NoViableAltException("", 26, 9, input);
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
							new NoViableAltException("", 26, 3, input);
						throw nvae;
					} finally {
						input.rewind(nvaeMark);
					}
				}

				}
				break;
			case WHILE:
				{
				alt26=5;
				}
				break;
			case IF:
				{
				alt26=6;
				}
				break;
			case ASSERT:
				{
				alt26=7;
				}
				break;
			default:
				if (state.backtracking>0) {state.failed=true; return retval;}
				NoViableAltException nvae =
					new NoViableAltException("", 26, 0, input);
				throw nvae;
			}
			switch (alt26) {
				case 1 :
					// Dafny.g:182:5: VAR ^ ID ':' ! type ( ':=' ! expression )? ';' !
					{
					root_0 = (DafnyTree)adaptor.nil();


					VAR63=(Token)match(input,VAR,FOLLOW_VAR_in_statement990); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					VAR63_tree = (DafnyTree)adaptor.create(VAR63);
					root_0 = (DafnyTree)adaptor.becomeRoot(VAR63_tree, root_0);
					}

					ID64=(Token)match(input,ID,FOLLOW_ID_in_statement993); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					ID64_tree = (DafnyTree)adaptor.create(ID64);
					adaptor.addChild(root_0, ID64_tree);
					}

					char_literal65=(Token)match(input,59,FOLLOW_59_in_statement995); if (state.failed) return retval;
					pushFollow(FOLLOW_type_in_statement998);
					type66=type();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, type66.getTree());

					// Dafny.g:182:23: ( ':=' ! expression )?
					int alt18=2;
					int LA18_0 = input.LA(1);
					if ( (LA18_0==ASSIGN) ) {
						alt18=1;
					}
					switch (alt18) {
						case 1 :
							// Dafny.g:182:24: ':=' ! expression
							{
							string_literal67=(Token)match(input,ASSIGN,FOLLOW_ASSIGN_in_statement1001); if (state.failed) return retval;
							pushFollow(FOLLOW_expression_in_statement1004);
							expression68=expression();
							state._fsp--;
							if (state.failed) return retval;
							if ( state.backtracking==0 ) adaptor.addChild(root_0, expression68.getTree());

							}
							break;

					}

					char_literal69=(Token)match(input,60,FOLLOW_60_in_statement1008); if (state.failed) return retval;
					}
					break;
				case 2 :
					// Dafny.g:183:5: ID ':=' ^ expression ';' !
					{
					root_0 = (DafnyTree)adaptor.nil();


					ID70=(Token)match(input,ID,FOLLOW_ID_in_statement1015); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					ID70_tree = (DafnyTree)adaptor.create(ID70);
					adaptor.addChild(root_0, ID70_tree);
					}

					string_literal71=(Token)match(input,ASSIGN,FOLLOW_ASSIGN_in_statement1017); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					string_literal71_tree = (DafnyTree)adaptor.create(string_literal71);
					root_0 = (DafnyTree)adaptor.becomeRoot(string_literal71_tree, root_0);
					}

					pushFollow(FOLLOW_expression_in_statement1020);
					expression72=expression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, expression72.getTree());

					char_literal73=(Token)match(input,60,FOLLOW_60_in_statement1022); if (state.failed) return retval;
					}
					break;
				case 3 :
					// Dafny.g:184:5: ( ID ':=' 'call' )=>r= ID ':=' 'call' f= ID '(' ( expressions )? ')' ';'
					{
					r=(Token)match(input,ID,FOLLOW_ID_in_statement1041); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_ID.add(r);

					string_literal74=(Token)match(input,ASSIGN,FOLLOW_ASSIGN_in_statement1043); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_ASSIGN.add(string_literal74);

					string_literal75=(Token)match(input,CALL,FOLLOW_CALL_in_statement1045); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_CALL.add(string_literal75);

					f=(Token)match(input,ID,FOLLOW_ID_in_statement1049); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_ID.add(f);

					char_literal76=(Token)match(input,56,FOLLOW_56_in_statement1051); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_56.add(char_literal76);

					// Dafny.g:184:51: ( expressions )?
					int alt19=2;
					int LA19_0 = input.LA(1);
					if ( (LA19_0==BLOCK_BEGIN||LA19_0==ID||LA19_0==LIT||LA19_0==MINUS||LA19_0==NOT||LA19_0==56||LA19_0==61) ) {
						alt19=1;
					}
					switch (alt19) {
						case 1 :
							// Dafny.g:184:51: expressions
							{
							pushFollow(FOLLOW_expressions_in_statement1053);
							expressions77=expressions();
							state._fsp--;
							if (state.failed) return retval;
							if ( state.backtracking==0 ) stream_expressions.add(expressions77.getTree());
							}
							break;

					}

					char_literal78=(Token)match(input,57,FOLLOW_57_in_statement1056); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_57.add(char_literal78);

					char_literal79=(Token)match(input,60,FOLLOW_60_in_statement1058); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_60.add(char_literal79);

					// AST REWRITE
					// elements: r, f, expressions, CALL
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
					// 185:9: -> ^( 'call' $f ^( RESULTS $r) ^( ARGS ( expressions )? ) )
					{
						// Dafny.g:185:12: ^( 'call' $f ^( RESULTS $r) ^( ARGS ( expressions )? ) )
						{
						DafnyTree root_1 = (DafnyTree)adaptor.nil();
						root_1 = (DafnyTree)adaptor.becomeRoot(stream_CALL.nextNode(), root_1);
						adaptor.addChild(root_1, stream_f.nextNode());
						// Dafny.g:185:24: ^( RESULTS $r)
						{
						DafnyTree root_2 = (DafnyTree)adaptor.nil();
						root_2 = (DafnyTree)adaptor.becomeRoot((DafnyTree)adaptor.create(RESULTS, "RESULTS"), root_2);
						adaptor.addChild(root_2, stream_r.nextNode());
						adaptor.addChild(root_1, root_2);
						}

						// Dafny.g:185:38: ^( ARGS ( expressions )? )
						{
						DafnyTree root_2 = (DafnyTree)adaptor.nil();
						root_2 = (DafnyTree)adaptor.becomeRoot((DafnyTree)adaptor.create(ARGS, "ARGS"), root_2);
						// Dafny.g:185:45: ( expressions )?
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
					// Dafny.g:186:5: ids ':=' 'call' ID '(' ( expressions )? ')' ';'
					{
					pushFollow(FOLLOW_ids_in_statement1095);
					ids80=ids();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_ids.add(ids80.getTree());
					string_literal81=(Token)match(input,ASSIGN,FOLLOW_ASSIGN_in_statement1097); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_ASSIGN.add(string_literal81);

					string_literal82=(Token)match(input,CALL,FOLLOW_CALL_in_statement1099); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_CALL.add(string_literal82);

					ID83=(Token)match(input,ID,FOLLOW_ID_in_statement1101); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_ID.add(ID83);

					char_literal84=(Token)match(input,56,FOLLOW_56_in_statement1103); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_56.add(char_literal84);

					// Dafny.g:186:28: ( expressions )?
					int alt20=2;
					int LA20_0 = input.LA(1);
					if ( (LA20_0==BLOCK_BEGIN||LA20_0==ID||LA20_0==LIT||LA20_0==MINUS||LA20_0==NOT||LA20_0==56||LA20_0==61) ) {
						alt20=1;
					}
					switch (alt20) {
						case 1 :
							// Dafny.g:186:28: expressions
							{
							pushFollow(FOLLOW_expressions_in_statement1105);
							expressions85=expressions();
							state._fsp--;
							if (state.failed) return retval;
							if ( state.backtracking==0 ) stream_expressions.add(expressions85.getTree());
							}
							break;

					}

					char_literal86=(Token)match(input,57,FOLLOW_57_in_statement1108); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_57.add(char_literal86);

					char_literal87=(Token)match(input,60,FOLLOW_60_in_statement1110); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_60.add(char_literal87);

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

					root_0 = (DafnyTree)adaptor.nil();
					// 187:9: -> ^( 'call' ID ^( RESULTS ids ) ^( ARGS ( expressions )? ) )
					{
						// Dafny.g:187:12: ^( 'call' ID ^( RESULTS ids ) ^( ARGS ( expressions )? ) )
						{
						DafnyTree root_1 = (DafnyTree)adaptor.nil();
						root_1 = (DafnyTree)adaptor.becomeRoot(stream_CALL.nextNode(), root_1);
						adaptor.addChild(root_1, stream_ID.nextNode());
						// Dafny.g:187:24: ^( RESULTS ids )
						{
						DafnyTree root_2 = (DafnyTree)adaptor.nil();
						root_2 = (DafnyTree)adaptor.becomeRoot((DafnyTree)adaptor.create(RESULTS, "RESULTS"), root_2);
						adaptor.addChild(root_2, stream_ids.nextTree());
						adaptor.addChild(root_1, root_2);
						}

						// Dafny.g:187:39: ^( ARGS ( expressions )? )
						{
						DafnyTree root_2 = (DafnyTree)adaptor.nil();
						root_2 = (DafnyTree)adaptor.becomeRoot((DafnyTree)adaptor.create(ARGS, "ARGS"), root_2);
						// Dafny.g:187:46: ( expressions )?
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
					// Dafny.g:188:5: ( label )? 'while' expression ( invariant )+ decreases relaxedBlock
					{
					// Dafny.g:188:5: ( label )?
					int alt21=2;
					int LA21_0 = input.LA(1);
					if ( (LA21_0==LABEL) ) {
						alt21=1;
					}
					switch (alt21) {
						case 1 :
							// Dafny.g:188:5: label
							{
							pushFollow(FOLLOW_label_in_statement1145);
							label88=label();
							state._fsp--;
							if (state.failed) return retval;
							if ( state.backtracking==0 ) stream_label.add(label88.getTree());
							}
							break;

					}

					string_literal89=(Token)match(input,WHILE,FOLLOW_WHILE_in_statement1154); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_WHILE.add(string_literal89);

					pushFollow(FOLLOW_expression_in_statement1156);
					expression90=expression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_expression.add(expression90.getTree());
					// Dafny.g:189:26: ( invariant )+
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
							// Dafny.g:189:26: invariant
							{
							pushFollow(FOLLOW_invariant_in_statement1158);
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

					pushFollow(FOLLOW_decreases_in_statement1161);
					decreases92=decreases();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_decreases.add(decreases92.getTree());
					pushFollow(FOLLOW_relaxedBlock_in_statement1163);
					relaxedBlock93=relaxedBlock();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_relaxedBlock.add(relaxedBlock93.getTree());
					// AST REWRITE
					// elements: relaxedBlock, label, WHILE, invariant, expression, decreases
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (DafnyTree)adaptor.nil();
					// 190:9: -> ^( 'while' ( label )? expression ( invariant )+ decreases relaxedBlock )
					{
						// Dafny.g:190:12: ^( 'while' ( label )? expression ( invariant )+ decreases relaxedBlock )
						{
						DafnyTree root_1 = (DafnyTree)adaptor.nil();
						root_1 = (DafnyTree)adaptor.becomeRoot(stream_WHILE.nextNode(), root_1);
						// Dafny.g:190:22: ( label )?
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
					// Dafny.g:191:5: ( label )? 'if' ^ expression relaxedBlock ( options {greedy=true; } : 'else' ! relaxedBlock )?
					{
					root_0 = (DafnyTree)adaptor.nil();


					// Dafny.g:191:5: ( label )?
					int alt23=2;
					int LA23_0 = input.LA(1);
					if ( (LA23_0==LABEL) ) {
						alt23=1;
					}
					switch (alt23) {
						case 1 :
							// Dafny.g:191:5: label
							{
							pushFollow(FOLLOW_label_in_statement1195);
							label94=label();
							state._fsp--;
							if (state.failed) return retval;
							if ( state.backtracking==0 ) adaptor.addChild(root_0, label94.getTree());

							}
							break;

					}

					string_literal95=(Token)match(input,IF,FOLLOW_IF_in_statement1198); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					string_literal95_tree = (DafnyTree)adaptor.create(string_literal95);
					root_0 = (DafnyTree)adaptor.becomeRoot(string_literal95_tree, root_0);
					}

					pushFollow(FOLLOW_expression_in_statement1201);
					expression96=expression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, expression96.getTree());

					pushFollow(FOLLOW_relaxedBlock_in_statement1203);
					relaxedBlock97=relaxedBlock();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, relaxedBlock97.getTree());

					// Dafny.g:192:7: ( options {greedy=true; } : 'else' ! relaxedBlock )?
					int alt24=2;
					int LA24_0 = input.LA(1);
					if ( (LA24_0==ELSE) ) {
						alt24=1;
					}
					switch (alt24) {
						case 1 :
							// Dafny.g:192:36: 'else' ! relaxedBlock
							{
							string_literal98=(Token)match(input,ELSE,FOLLOW_ELSE_in_statement1224); if (state.failed) return retval;
							pushFollow(FOLLOW_relaxedBlock_in_statement1227);
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
					// Dafny.g:193:5: 'assert' ^ ( 'label' ! ID ':' !)? expression ';' !
					{
					root_0 = (DafnyTree)adaptor.nil();


					string_literal100=(Token)match(input,ASSERT,FOLLOW_ASSERT_in_statement1236); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					string_literal100_tree = (DafnyTree)adaptor.create(string_literal100);
					root_0 = (DafnyTree)adaptor.becomeRoot(string_literal100_tree, root_0);
					}

					// Dafny.g:193:15: ( 'label' ! ID ':' !)?
					int alt25=2;
					int LA25_0 = input.LA(1);
					if ( (LA25_0==LABEL) ) {
						alt25=1;
					}
					switch (alt25) {
						case 1 :
							// Dafny.g:193:17: 'label' ! ID ':' !
							{
							string_literal101=(Token)match(input,LABEL,FOLLOW_LABEL_in_statement1241); if (state.failed) return retval;
							ID102=(Token)match(input,ID,FOLLOW_ID_in_statement1244); if (state.failed) return retval;
							if ( state.backtracking==0 ) {
							ID102_tree = (DafnyTree)adaptor.create(ID102);
							adaptor.addChild(root_0, ID102_tree);
							}

							char_literal103=(Token)match(input,59,FOLLOW_59_in_statement1246); if (state.failed) return retval;
							}
							break;

					}

					pushFollow(FOLLOW_expression_in_statement1252);
					expression104=expression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, expression104.getTree());

					char_literal105=(Token)match(input,60,FOLLOW_60_in_statement1254); if (state.failed) return retval;
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
	// Dafny.g:196:1: ids : ID ( ',' ! ID )+ ;
	public final DafnyParser.ids_return ids() throws RecognitionException {
		DafnyParser.ids_return retval = new DafnyParser.ids_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		Token ID106=null;
		Token char_literal107=null;
		Token ID108=null;

		DafnyTree ID106_tree=null;
		DafnyTree char_literal107_tree=null;
		DafnyTree ID108_tree=null;

		try {
			// Dafny.g:196:4: ( ID ( ',' ! ID )+ )
			// Dafny.g:197:3: ID ( ',' ! ID )+
			{
			root_0 = (DafnyTree)adaptor.nil();


			ID106=(Token)match(input,ID,FOLLOW_ID_in_ids1267); if (state.failed) return retval;
			if ( state.backtracking==0 ) {
			ID106_tree = (DafnyTree)adaptor.create(ID106);
			adaptor.addChild(root_0, ID106_tree);
			}

			// Dafny.g:197:6: ( ',' ! ID )+
			int cnt27=0;
			loop27:
			while (true) {
				int alt27=2;
				int LA27_0 = input.LA(1);
				if ( (LA27_0==58) ) {
					alt27=1;
				}

				switch (alt27) {
				case 1 :
					// Dafny.g:197:7: ',' ! ID
					{
					char_literal107=(Token)match(input,58,FOLLOW_58_in_ids1270); if (state.failed) return retval;
					ID108=(Token)match(input,ID,FOLLOW_ID_in_ids1273); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					ID108_tree = (DafnyTree)adaptor.create(ID108);
					adaptor.addChild(root_0, ID108_tree);
					}

					}
					break;

				default :
					if ( cnt27 >= 1 ) break loop27;
					if (state.backtracking>0) {state.failed=true; return retval;}
					EarlyExitException eee = new EarlyExitException(27, input);
					throw eee;
				}
				cnt27++;
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
	// Dafny.g:200:1: expressions : expression ( ',' ! expression )* ;
	public final DafnyParser.expressions_return expressions() throws RecognitionException {
		DafnyParser.expressions_return retval = new DafnyParser.expressions_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		Token char_literal110=null;
		ParserRuleReturnScope expression109 =null;
		ParserRuleReturnScope expression111 =null;

		DafnyTree char_literal110_tree=null;

		try {
			// Dafny.g:200:12: ( expression ( ',' ! expression )* )
			// Dafny.g:201:3: expression ( ',' ! expression )*
			{
			root_0 = (DafnyTree)adaptor.nil();


			pushFollow(FOLLOW_expression_in_expressions1287);
			expression109=expression();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, expression109.getTree());

			// Dafny.g:201:14: ( ',' ! expression )*
			loop28:
			while (true) {
				int alt28=2;
				int LA28_0 = input.LA(1);
				if ( (LA28_0==58) ) {
					alt28=1;
				}

				switch (alt28) {
				case 1 :
					// Dafny.g:201:16: ',' ! expression
					{
					char_literal110=(Token)match(input,58,FOLLOW_58_in_expressions1291); if (state.failed) return retval;
					pushFollow(FOLLOW_expression_in_expressions1294);
					expression111=expression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, expression111.getTree());

					}
					break;

				default :
					break loop28;
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
	// Dafny.g:204:1: expression : or_expr ;
	public final DafnyParser.expression_return expression() throws RecognitionException {
		DafnyParser.expression_return retval = new DafnyParser.expression_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		ParserRuleReturnScope or_expr112 =null;


		try {
			// Dafny.g:204:11: ( or_expr )
			// Dafny.g:205:3: or_expr
			{
			root_0 = (DafnyTree)adaptor.nil();


			pushFollow(FOLLOW_or_expr_in_expression1309);
			or_expr112=or_expr();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, or_expr112.getTree());

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
	// Dafny.g:207:1: or_expr : and_expr ( ( '||' ^| '==>' ^) or_expr )? ;
	public final DafnyParser.or_expr_return or_expr() throws RecognitionException {
		DafnyParser.or_expr_return retval = new DafnyParser.or_expr_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		Token string_literal114=null;
		Token string_literal115=null;
		ParserRuleReturnScope and_expr113 =null;
		ParserRuleReturnScope or_expr116 =null;

		DafnyTree string_literal114_tree=null;
		DafnyTree string_literal115_tree=null;

		try {
			// Dafny.g:207:8: ( and_expr ( ( '||' ^| '==>' ^) or_expr )? )
			// Dafny.g:208:3: and_expr ( ( '||' ^| '==>' ^) or_expr )?
			{
			root_0 = (DafnyTree)adaptor.nil();


			pushFollow(FOLLOW_and_expr_in_or_expr1318);
			and_expr113=and_expr();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, and_expr113.getTree());

			// Dafny.g:208:12: ( ( '||' ^| '==>' ^) or_expr )?
			int alt30=2;
			int LA30_0 = input.LA(1);
			if ( (LA30_0==IMPLIES||LA30_0==OR) ) {
				alt30=1;
			}
			switch (alt30) {
				case 1 :
					// Dafny.g:208:14: ( '||' ^| '==>' ^) or_expr
					{
					// Dafny.g:208:14: ( '||' ^| '==>' ^)
					int alt29=2;
					int LA29_0 = input.LA(1);
					if ( (LA29_0==OR) ) {
						alt29=1;
					}
					else if ( (LA29_0==IMPLIES) ) {
						alt29=2;
					}

					else {
						if (state.backtracking>0) {state.failed=true; return retval;}
						NoViableAltException nvae =
							new NoViableAltException("", 29, 0, input);
						throw nvae;
					}

					switch (alt29) {
						case 1 :
							// Dafny.g:208:15: '||' ^
							{
							string_literal114=(Token)match(input,OR,FOLLOW_OR_in_or_expr1323); if (state.failed) return retval;
							if ( state.backtracking==0 ) {
							string_literal114_tree = (DafnyTree)adaptor.create(string_literal114);
							root_0 = (DafnyTree)adaptor.becomeRoot(string_literal114_tree, root_0);
							}

							}
							break;
						case 2 :
							// Dafny.g:208:23: '==>' ^
							{
							string_literal115=(Token)match(input,IMPLIES,FOLLOW_IMPLIES_in_or_expr1328); if (state.failed) return retval;
							if ( state.backtracking==0 ) {
							string_literal115_tree = (DafnyTree)adaptor.create(string_literal115);
							root_0 = (DafnyTree)adaptor.becomeRoot(string_literal115_tree, root_0);
							}

							}
							break;

					}

					pushFollow(FOLLOW_or_expr_in_or_expr1332);
					or_expr116=or_expr();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, or_expr116.getTree());

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
	// Dafny.g:211:1: and_expr : rel_expr ( '&&' ^ and_expr )? ;
	public final DafnyParser.and_expr_return and_expr() throws RecognitionException {
		DafnyParser.and_expr_return retval = new DafnyParser.and_expr_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		Token string_literal118=null;
		ParserRuleReturnScope rel_expr117 =null;
		ParserRuleReturnScope and_expr119 =null;

		DafnyTree string_literal118_tree=null;

		try {
			// Dafny.g:211:9: ( rel_expr ( '&&' ^ and_expr )? )
			// Dafny.g:212:3: rel_expr ( '&&' ^ and_expr )?
			{
			root_0 = (DafnyTree)adaptor.nil();


			pushFollow(FOLLOW_rel_expr_in_and_expr1347);
			rel_expr117=rel_expr();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, rel_expr117.getTree());

			// Dafny.g:212:12: ( '&&' ^ and_expr )?
			int alt31=2;
			int LA31_0 = input.LA(1);
			if ( (LA31_0==AND) ) {
				alt31=1;
			}
			switch (alt31) {
				case 1 :
					// Dafny.g:212:14: '&&' ^ and_expr
					{
					string_literal118=(Token)match(input,AND,FOLLOW_AND_in_and_expr1351); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					string_literal118_tree = (DafnyTree)adaptor.create(string_literal118);
					root_0 = (DafnyTree)adaptor.becomeRoot(string_literal118_tree, root_0);
					}

					pushFollow(FOLLOW_and_expr_in_and_expr1354);
					and_expr119=and_expr();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, and_expr119.getTree());

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
	// Dafny.g:215:1: rel_expr : add_expr ( ( '<' ^| '>' ^| '==' ^| '<=' ^| '>=' ^) add_expr )? ;
	public final DafnyParser.rel_expr_return rel_expr() throws RecognitionException {
		DafnyParser.rel_expr_return retval = new DafnyParser.rel_expr_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		Token char_literal121=null;
		Token char_literal122=null;
		Token string_literal123=null;
		Token string_literal124=null;
		Token string_literal125=null;
		ParserRuleReturnScope add_expr120 =null;
		ParserRuleReturnScope add_expr126 =null;

		DafnyTree char_literal121_tree=null;
		DafnyTree char_literal122_tree=null;
		DafnyTree string_literal123_tree=null;
		DafnyTree string_literal124_tree=null;
		DafnyTree string_literal125_tree=null;

		try {
			// Dafny.g:215:9: ( add_expr ( ( '<' ^| '>' ^| '==' ^| '<=' ^| '>=' ^) add_expr )? )
			// Dafny.g:216:3: add_expr ( ( '<' ^| '>' ^| '==' ^| '<=' ^| '>=' ^) add_expr )?
			{
			root_0 = (DafnyTree)adaptor.nil();


			pushFollow(FOLLOW_add_expr_in_rel_expr1369);
			add_expr120=add_expr();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, add_expr120.getTree());

			// Dafny.g:216:12: ( ( '<' ^| '>' ^| '==' ^| '<=' ^| '>=' ^) add_expr )?
			int alt33=2;
			int LA33_0 = input.LA(1);
			if ( (LA33_0==EQ||(LA33_0 >= GE && LA33_0 <= GT)||LA33_0==LE||LA33_0==LT) ) {
				alt33=1;
			}
			switch (alt33) {
				case 1 :
					// Dafny.g:216:14: ( '<' ^| '>' ^| '==' ^| '<=' ^| '>=' ^) add_expr
					{
					// Dafny.g:216:14: ( '<' ^| '>' ^| '==' ^| '<=' ^| '>=' ^)
					int alt32=5;
					switch ( input.LA(1) ) {
					case LT:
						{
						alt32=1;
						}
						break;
					case GT:
						{
						alt32=2;
						}
						break;
					case EQ:
						{
						alt32=3;
						}
						break;
					case LE:
						{
						alt32=4;
						}
						break;
					case GE:
						{
						alt32=5;
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
							// Dafny.g:216:15: '<' ^
							{
							char_literal121=(Token)match(input,LT,FOLLOW_LT_in_rel_expr1374); if (state.failed) return retval;
							if ( state.backtracking==0 ) {
							char_literal121_tree = (DafnyTree)adaptor.create(char_literal121);
							root_0 = (DafnyTree)adaptor.becomeRoot(char_literal121_tree, root_0);
							}

							}
							break;
						case 2 :
							// Dafny.g:216:22: '>' ^
							{
							char_literal122=(Token)match(input,GT,FOLLOW_GT_in_rel_expr1379); if (state.failed) return retval;
							if ( state.backtracking==0 ) {
							char_literal122_tree = (DafnyTree)adaptor.create(char_literal122);
							root_0 = (DafnyTree)adaptor.becomeRoot(char_literal122_tree, root_0);
							}

							}
							break;
						case 3 :
							// Dafny.g:216:29: '==' ^
							{
							string_literal123=(Token)match(input,EQ,FOLLOW_EQ_in_rel_expr1384); if (state.failed) return retval;
							if ( state.backtracking==0 ) {
							string_literal123_tree = (DafnyTree)adaptor.create(string_literal123);
							root_0 = (DafnyTree)adaptor.becomeRoot(string_literal123_tree, root_0);
							}

							}
							break;
						case 4 :
							// Dafny.g:216:37: '<=' ^
							{
							string_literal124=(Token)match(input,LE,FOLLOW_LE_in_rel_expr1389); if (state.failed) return retval;
							if ( state.backtracking==0 ) {
							string_literal124_tree = (DafnyTree)adaptor.create(string_literal124);
							root_0 = (DafnyTree)adaptor.becomeRoot(string_literal124_tree, root_0);
							}

							}
							break;
						case 5 :
							// Dafny.g:216:45: '>=' ^
							{
							string_literal125=(Token)match(input,GE,FOLLOW_GE_in_rel_expr1394); if (state.failed) return retval;
							if ( state.backtracking==0 ) {
							string_literal125_tree = (DafnyTree)adaptor.create(string_literal125);
							root_0 = (DafnyTree)adaptor.becomeRoot(string_literal125_tree, root_0);
							}

							}
							break;

					}

					pushFollow(FOLLOW_add_expr_in_rel_expr1398);
					add_expr126=add_expr();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, add_expr126.getTree());

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
	// Dafny.g:219:1: add_expr : mul_expr ( ( '+' | '-' | '++' ) ^ add_expr )? ;
	public final DafnyParser.add_expr_return add_expr() throws RecognitionException {
		DafnyParser.add_expr_return retval = new DafnyParser.add_expr_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		Token set128=null;
		ParserRuleReturnScope mul_expr127 =null;
		ParserRuleReturnScope add_expr129 =null;

		DafnyTree set128_tree=null;

		try {
			// Dafny.g:219:9: ( mul_expr ( ( '+' | '-' | '++' ) ^ add_expr )? )
			// Dafny.g:220:3: mul_expr ( ( '+' | '-' | '++' ) ^ add_expr )?
			{
			root_0 = (DafnyTree)adaptor.nil();


			pushFollow(FOLLOW_mul_expr_in_add_expr1413);
			mul_expr127=mul_expr();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, mul_expr127.getTree());

			// Dafny.g:220:12: ( ( '+' | '-' | '++' ) ^ add_expr )?
			int alt34=2;
			int LA34_0 = input.LA(1);
			if ( (LA34_0==MINUS||LA34_0==PLUS||LA34_0==UNION) ) {
				alt34=1;
			}
			switch (alt34) {
				case 1 :
					// Dafny.g:220:14: ( '+' | '-' | '++' ) ^ add_expr
					{
					set128=input.LT(1);
					set128=input.LT(1);
					if ( input.LA(1)==MINUS||input.LA(1)==PLUS||input.LA(1)==UNION ) {
						input.consume();
						if ( state.backtracking==0 ) root_0 = (DafnyTree)adaptor.becomeRoot((DafnyTree)adaptor.create(set128), root_0);
						state.errorRecovery=false;
						state.failed=false;
					}
					else {
						if (state.backtracking>0) {state.failed=true; return retval;}
						MismatchedSetException mse = new MismatchedSetException(null,input);
						throw mse;
					}
					pushFollow(FOLLOW_add_expr_in_add_expr1430);
					add_expr129=add_expr();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, add_expr129.getTree());

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
	// Dafny.g:223:1: mul_expr : prefix_expr ( ( '*' | '**' ) ^ mul_expr )? ;
	public final DafnyParser.mul_expr_return mul_expr() throws RecognitionException {
		DafnyParser.mul_expr_return retval = new DafnyParser.mul_expr_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		Token set131=null;
		ParserRuleReturnScope prefix_expr130 =null;
		ParserRuleReturnScope mul_expr132 =null;

		DafnyTree set131_tree=null;

		try {
			// Dafny.g:223:9: ( prefix_expr ( ( '*' | '**' ) ^ mul_expr )? )
			// Dafny.g:224:3: prefix_expr ( ( '*' | '**' ) ^ mul_expr )?
			{
			root_0 = (DafnyTree)adaptor.nil();


			pushFollow(FOLLOW_prefix_expr_in_mul_expr1445);
			prefix_expr130=prefix_expr();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, prefix_expr130.getTree());

			// Dafny.g:224:15: ( ( '*' | '**' ) ^ mul_expr )?
			int alt35=2;
			int LA35_0 = input.LA(1);
			if ( (LA35_0==INTERSECT||LA35_0==TIMES) ) {
				alt35=1;
			}
			switch (alt35) {
				case 1 :
					// Dafny.g:224:17: ( '*' | '**' ) ^ mul_expr
					{
					set131=input.LT(1);
					set131=input.LT(1);
					if ( input.LA(1)==INTERSECT||input.LA(1)==TIMES ) {
						input.consume();
						if ( state.backtracking==0 ) root_0 = (DafnyTree)adaptor.becomeRoot((DafnyTree)adaptor.create(set131), root_0);
						state.errorRecovery=false;
						state.failed=false;
					}
					else {
						if (state.backtracking>0) {state.failed=true; return retval;}
						MismatchedSetException mse = new MismatchedSetException(null,input);
						throw mse;
					}
					pushFollow(FOLLOW_mul_expr_in_mul_expr1458);
					mul_expr132=mul_expr();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, mul_expr132.getTree());

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
	// Dafny.g:227:1: prefix_expr : ( '-' ^ prefix_expr | '!' ^ prefix_expr | postfix_expr );
	public final DafnyParser.prefix_expr_return prefix_expr() throws RecognitionException {
		DafnyParser.prefix_expr_return retval = new DafnyParser.prefix_expr_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		Token char_literal133=null;
		Token char_literal135=null;
		ParserRuleReturnScope prefix_expr134 =null;
		ParserRuleReturnScope prefix_expr136 =null;
		ParserRuleReturnScope postfix_expr137 =null;

		DafnyTree char_literal133_tree=null;
		DafnyTree char_literal135_tree=null;

		try {
			// Dafny.g:227:12: ( '-' ^ prefix_expr | '!' ^ prefix_expr | postfix_expr )
			int alt36=3;
			switch ( input.LA(1) ) {
			case MINUS:
				{
				alt36=1;
				}
				break;
			case NOT:
				{
				alt36=2;
				}
				break;
			case BLOCK_BEGIN:
			case ID:
			case LIT:
			case 56:
			case 61:
				{
				alt36=3;
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
					// Dafny.g:228:5: '-' ^ prefix_expr
					{
					root_0 = (DafnyTree)adaptor.nil();


					char_literal133=(Token)match(input,MINUS,FOLLOW_MINUS_in_prefix_expr1475); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					char_literal133_tree = (DafnyTree)adaptor.create(char_literal133);
					root_0 = (DafnyTree)adaptor.becomeRoot(char_literal133_tree, root_0);
					}

					pushFollow(FOLLOW_prefix_expr_in_prefix_expr1478);
					prefix_expr134=prefix_expr();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, prefix_expr134.getTree());

					}
					break;
				case 2 :
					// Dafny.g:229:5: '!' ^ prefix_expr
					{
					root_0 = (DafnyTree)adaptor.nil();


					char_literal135=(Token)match(input,NOT,FOLLOW_NOT_in_prefix_expr1484); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					char_literal135_tree = (DafnyTree)adaptor.create(char_literal135);
					root_0 = (DafnyTree)adaptor.becomeRoot(char_literal135_tree, root_0);
					}

					pushFollow(FOLLOW_prefix_expr_in_prefix_expr1487);
					prefix_expr136=prefix_expr();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, prefix_expr136.getTree());

					}
					break;
				case 3 :
					// Dafny.g:230:5: postfix_expr
					{
					root_0 = (DafnyTree)adaptor.nil();


					pushFollow(FOLLOW_postfix_expr_in_prefix_expr1493);
					postfix_expr137=postfix_expr();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, postfix_expr137.getTree());

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
	// Dafny.g:233:1: postfix_expr : atom_expr ( '[' expression ']' -> ^( ARRAY_ACCESS atom_expr expression ) | '.' LENGTH -> ^( LENGTH atom_expr ) | -> atom_expr | EOF -> atom_expr ) ;
	public final DafnyParser.postfix_expr_return postfix_expr() throws RecognitionException {
		DafnyParser.postfix_expr_return retval = new DafnyParser.postfix_expr_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		Token char_literal139=null;
		Token char_literal141=null;
		Token char_literal142=null;
		Token LENGTH143=null;
		Token EOF144=null;
		ParserRuleReturnScope atom_expr138 =null;
		ParserRuleReturnScope expression140 =null;

		DafnyTree char_literal139_tree=null;
		DafnyTree char_literal141_tree=null;
		DafnyTree char_literal142_tree=null;
		DafnyTree LENGTH143_tree=null;
		DafnyTree EOF144_tree=null;
		RewriteRuleTokenStream stream_DOT=new RewriteRuleTokenStream(adaptor,"token DOT");
		RewriteRuleTokenStream stream_EOF=new RewriteRuleTokenStream(adaptor,"token EOF");
		RewriteRuleTokenStream stream_62=new RewriteRuleTokenStream(adaptor,"token 62");
		RewriteRuleTokenStream stream_LENGTH=new RewriteRuleTokenStream(adaptor,"token LENGTH");
		RewriteRuleTokenStream stream_61=new RewriteRuleTokenStream(adaptor,"token 61");
		RewriteRuleSubtreeStream stream_expression=new RewriteRuleSubtreeStream(adaptor,"rule expression");
		RewriteRuleSubtreeStream stream_atom_expr=new RewriteRuleSubtreeStream(adaptor,"rule atom_expr");

		try {
			// Dafny.g:233:13: ( atom_expr ( '[' expression ']' -> ^( ARRAY_ACCESS atom_expr expression ) | '.' LENGTH -> ^( LENGTH atom_expr ) | -> atom_expr | EOF -> atom_expr ) )
			// Dafny.g:234:3: atom_expr ( '[' expression ']' -> ^( ARRAY_ACCESS atom_expr expression ) | '.' LENGTH -> ^( LENGTH atom_expr ) | -> atom_expr | EOF -> atom_expr )
			{
			pushFollow(FOLLOW_atom_expr_in_postfix_expr1505);
			atom_expr138=atom_expr();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) stream_atom_expr.add(atom_expr138.getTree());
			// Dafny.g:235:3: ( '[' expression ']' -> ^( ARRAY_ACCESS atom_expr expression ) | '.' LENGTH -> ^( LENGTH atom_expr ) | -> atom_expr | EOF -> atom_expr )
			int alt37=4;
			switch ( input.LA(1) ) {
			case 61:
				{
				alt37=1;
				}
				break;
			case DOT:
				{
				alt37=2;
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
			case VAR:
			case WHILE:
			case 57:
			case 58:
			case 60:
			case 62:
				{
				alt37=3;
				}
				break;
			case EOF:
				{
				alt37=4;
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
					// Dafny.g:235:5: '[' expression ']'
					{
					char_literal139=(Token)match(input,61,FOLLOW_61_in_postfix_expr1511); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_61.add(char_literal139);

					pushFollow(FOLLOW_expression_in_postfix_expr1513);
					expression140=expression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_expression.add(expression140.getTree());
					char_literal141=(Token)match(input,62,FOLLOW_62_in_postfix_expr1515); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_62.add(char_literal141);

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
					// 235:24: -> ^( ARRAY_ACCESS atom_expr expression )
					{
						// Dafny.g:235:27: ^( ARRAY_ACCESS atom_expr expression )
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
					// Dafny.g:236:5: '.' LENGTH
					{
					char_literal142=(Token)match(input,DOT,FOLLOW_DOT_in_postfix_expr1533); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_DOT.add(char_literal142);

					LENGTH143=(Token)match(input,LENGTH,FOLLOW_LENGTH_in_postfix_expr1535); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_LENGTH.add(LENGTH143);

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
					// 236:16: -> ^( LENGTH atom_expr )
					{
						// Dafny.g:236:19: ^( LENGTH atom_expr )
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
					// Dafny.g:237:5: 
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
					// 237:5: -> atom_expr
					{
						adaptor.addChild(root_0, stream_atom_expr.nextTree());
					}


					retval.tree = root_0;
					}

					}
					break;
				case 4 :
					// Dafny.g:238:5: EOF
					{
					EOF144=(Token)match(input,EOF,FOLLOW_EOF_in_postfix_expr1559); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_EOF.add(EOF144);

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
					// 238:9: -> atom_expr
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
	// Dafny.g:242:1: atom_expr : ( ID | LIT | quantifier | '(' ! expression ')' !| '{' ( expressions )? '}' -> ^( SETEX ( expressions )? ) | '[' ( expressions )? ']' -> ^( LISTEX ( expressions )? ) );
	public final DafnyParser.atom_expr_return atom_expr() throws RecognitionException {
		DafnyParser.atom_expr_return retval = new DafnyParser.atom_expr_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		Token ID145=null;
		Token LIT146=null;
		Token char_literal148=null;
		Token char_literal150=null;
		Token char_literal151=null;
		Token char_literal153=null;
		Token char_literal154=null;
		Token char_literal156=null;
		ParserRuleReturnScope quantifier147 =null;
		ParserRuleReturnScope expression149 =null;
		ParserRuleReturnScope expressions152 =null;
		ParserRuleReturnScope expressions155 =null;

		DafnyTree ID145_tree=null;
		DafnyTree LIT146_tree=null;
		DafnyTree char_literal148_tree=null;
		DafnyTree char_literal150_tree=null;
		DafnyTree char_literal151_tree=null;
		DafnyTree char_literal153_tree=null;
		DafnyTree char_literal154_tree=null;
		DafnyTree char_literal156_tree=null;
		RewriteRuleTokenStream stream_62=new RewriteRuleTokenStream(adaptor,"token 62");
		RewriteRuleTokenStream stream_BLOCK_BEGIN=new RewriteRuleTokenStream(adaptor,"token BLOCK_BEGIN");
		RewriteRuleTokenStream stream_61=new RewriteRuleTokenStream(adaptor,"token 61");
		RewriteRuleTokenStream stream_BLOCK_END=new RewriteRuleTokenStream(adaptor,"token BLOCK_END");
		RewriteRuleSubtreeStream stream_expressions=new RewriteRuleSubtreeStream(adaptor,"rule expressions");

		try {
			// Dafny.g:242:10: ( ID | LIT | quantifier | '(' ! expression ')' !| '{' ( expressions )? '}' -> ^( SETEX ( expressions )? ) | '[' ( expressions )? ']' -> ^( LISTEX ( expressions )? ) )
			int alt40=6;
			switch ( input.LA(1) ) {
			case ID:
				{
				alt40=1;
				}
				break;
			case LIT:
				{
				alt40=2;
				}
				break;
			case 56:
				{
				int LA40_3 = input.LA(2);
				if ( (LA40_3==ALL||LA40_3==EX) ) {
					alt40=3;
				}
				else if ( (LA40_3==BLOCK_BEGIN||LA40_3==ID||LA40_3==LIT||LA40_3==MINUS||LA40_3==NOT||LA40_3==56||LA40_3==61) ) {
					alt40=4;
				}

				else {
					if (state.backtracking>0) {state.failed=true; return retval;}
					int nvaeMark = input.mark();
					try {
						input.consume();
						NoViableAltException nvae =
							new NoViableAltException("", 40, 3, input);
						throw nvae;
					} finally {
						input.rewind(nvaeMark);
					}
				}

				}
				break;
			case BLOCK_BEGIN:
				{
				alt40=5;
				}
				break;
			case 61:
				{
				alt40=6;
				}
				break;
			default:
				if (state.backtracking>0) {state.failed=true; return retval;}
				NoViableAltException nvae =
					new NoViableAltException("", 40, 0, input);
				throw nvae;
			}
			switch (alt40) {
				case 1 :
					// Dafny.g:243:5: ID
					{
					root_0 = (DafnyTree)adaptor.nil();


					ID145=(Token)match(input,ID,FOLLOW_ID_in_atom_expr1581); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					ID145_tree = (DafnyTree)adaptor.create(ID145);
					adaptor.addChild(root_0, ID145_tree);
					}

					}
					break;
				case 2 :
					// Dafny.g:244:5: LIT
					{
					root_0 = (DafnyTree)adaptor.nil();


					LIT146=(Token)match(input,LIT,FOLLOW_LIT_in_atom_expr1587); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					LIT146_tree = (DafnyTree)adaptor.create(LIT146);
					adaptor.addChild(root_0, LIT146_tree);
					}

					}
					break;
				case 3 :
					// Dafny.g:245:5: quantifier
					{
					root_0 = (DafnyTree)adaptor.nil();


					pushFollow(FOLLOW_quantifier_in_atom_expr1593);
					quantifier147=quantifier();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, quantifier147.getTree());

					}
					break;
				case 4 :
					// Dafny.g:246:5: '(' ! expression ')' !
					{
					root_0 = (DafnyTree)adaptor.nil();


					char_literal148=(Token)match(input,56,FOLLOW_56_in_atom_expr1599); if (state.failed) return retval;
					pushFollow(FOLLOW_expression_in_atom_expr1602);
					expression149=expression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, expression149.getTree());

					char_literal150=(Token)match(input,57,FOLLOW_57_in_atom_expr1604); if (state.failed) return retval;
					}
					break;
				case 5 :
					// Dafny.g:247:5: '{' ( expressions )? '}'
					{
					char_literal151=(Token)match(input,BLOCK_BEGIN,FOLLOW_BLOCK_BEGIN_in_atom_expr1611); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_BLOCK_BEGIN.add(char_literal151);

					// Dafny.g:247:9: ( expressions )?
					int alt38=2;
					int LA38_0 = input.LA(1);
					if ( (LA38_0==BLOCK_BEGIN||LA38_0==ID||LA38_0==LIT||LA38_0==MINUS||LA38_0==NOT||LA38_0==56||LA38_0==61) ) {
						alt38=1;
					}
					switch (alt38) {
						case 1 :
							// Dafny.g:247:9: expressions
							{
							pushFollow(FOLLOW_expressions_in_atom_expr1613);
							expressions152=expressions();
							state._fsp--;
							if (state.failed) return retval;
							if ( state.backtracking==0 ) stream_expressions.add(expressions152.getTree());
							}
							break;

					}

					char_literal153=(Token)match(input,BLOCK_END,FOLLOW_BLOCK_END_in_atom_expr1616); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_BLOCK_END.add(char_literal153);

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
					// 247:26: -> ^( SETEX ( expressions )? )
					{
						// Dafny.g:247:29: ^( SETEX ( expressions )? )
						{
						DafnyTree root_1 = (DafnyTree)adaptor.nil();
						root_1 = (DafnyTree)adaptor.becomeRoot((DafnyTree)adaptor.create(SETEX, "SETEX"), root_1);
						// Dafny.g:247:37: ( expressions )?
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
					// Dafny.g:248:5: '[' ( expressions )? ']'
					{
					char_literal154=(Token)match(input,61,FOLLOW_61_in_atom_expr1631); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_61.add(char_literal154);

					// Dafny.g:248:9: ( expressions )?
					int alt39=2;
					int LA39_0 = input.LA(1);
					if ( (LA39_0==BLOCK_BEGIN||LA39_0==ID||LA39_0==LIT||LA39_0==MINUS||LA39_0==NOT||LA39_0==56||LA39_0==61) ) {
						alt39=1;
					}
					switch (alt39) {
						case 1 :
							// Dafny.g:248:9: expressions
							{
							pushFollow(FOLLOW_expressions_in_atom_expr1633);
							expressions155=expressions();
							state._fsp--;
							if (state.failed) return retval;
							if ( state.backtracking==0 ) stream_expressions.add(expressions155.getTree());
							}
							break;

					}

					char_literal156=(Token)match(input,62,FOLLOW_62_in_atom_expr1636); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_62.add(char_literal156);

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
					// 248:26: -> ^( LISTEX ( expressions )? )
					{
						// Dafny.g:248:29: ^( LISTEX ( expressions )? )
						{
						DafnyTree root_1 = (DafnyTree)adaptor.nil();
						root_1 = (DafnyTree)adaptor.becomeRoot((DafnyTree)adaptor.create(LISTEX, "LISTEX"), root_1);
						// Dafny.g:248:38: ( expressions )?
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
	// Dafny.g:251:1: quantifier : '(' ! ( ALL ^| EX ^) ID ':' ! type '::' ! expression ')' !;
	public final DafnyParser.quantifier_return quantifier() throws RecognitionException {
		DafnyParser.quantifier_return retval = new DafnyParser.quantifier_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		Token char_literal157=null;
		Token ALL158=null;
		Token EX159=null;
		Token ID160=null;
		Token char_literal161=null;
		Token string_literal163=null;
		Token char_literal165=null;
		ParserRuleReturnScope type162 =null;
		ParserRuleReturnScope expression164 =null;

		DafnyTree char_literal157_tree=null;
		DafnyTree ALL158_tree=null;
		DafnyTree EX159_tree=null;
		DafnyTree ID160_tree=null;
		DafnyTree char_literal161_tree=null;
		DafnyTree string_literal163_tree=null;
		DafnyTree char_literal165_tree=null;

		try {
			// Dafny.g:251:11: ( '(' ! ( ALL ^| EX ^) ID ':' ! type '::' ! expression ')' !)
			// Dafny.g:252:3: '(' ! ( ALL ^| EX ^) ID ':' ! type '::' ! expression ')' !
			{
			root_0 = (DafnyTree)adaptor.nil();


			char_literal157=(Token)match(input,56,FOLLOW_56_in_quantifier1657); if (state.failed) return retval;
			// Dafny.g:252:8: ( ALL ^| EX ^)
			int alt41=2;
			int LA41_0 = input.LA(1);
			if ( (LA41_0==ALL) ) {
				alt41=1;
			}
			else if ( (LA41_0==EX) ) {
				alt41=2;
			}

			else {
				if (state.backtracking>0) {state.failed=true; return retval;}
				NoViableAltException nvae =
					new NoViableAltException("", 41, 0, input);
				throw nvae;
			}

			switch (alt41) {
				case 1 :
					// Dafny.g:252:9: ALL ^
					{
					ALL158=(Token)match(input,ALL,FOLLOW_ALL_in_quantifier1661); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					ALL158_tree = (DafnyTree)adaptor.create(ALL158);
					root_0 = (DafnyTree)adaptor.becomeRoot(ALL158_tree, root_0);
					}

					}
					break;
				case 2 :
					// Dafny.g:252:16: EX ^
					{
					EX159=(Token)match(input,EX,FOLLOW_EX_in_quantifier1666); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					EX159_tree = (DafnyTree)adaptor.create(EX159);
					root_0 = (DafnyTree)adaptor.becomeRoot(EX159_tree, root_0);
					}

					}
					break;

			}

			ID160=(Token)match(input,ID,FOLLOW_ID_in_quantifier1670); if (state.failed) return retval;
			if ( state.backtracking==0 ) {
			ID160_tree = (DafnyTree)adaptor.create(ID160);
			adaptor.addChild(root_0, ID160_tree);
			}

			char_literal161=(Token)match(input,59,FOLLOW_59_in_quantifier1672); if (state.failed) return retval;
			pushFollow(FOLLOW_type_in_quantifier1675);
			type162=type();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, type162.getTree());

			string_literal163=(Token)match(input,DOUBLECOLON,FOLLOW_DOUBLECOLON_in_quantifier1677); if (state.failed) return retval;
			pushFollow(FOLLOW_expression_in_quantifier1680);
			expression164=expression();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, expression164.getTree());

			char_literal165=(Token)match(input,57,FOLLOW_57_in_quantifier1682); if (state.failed) return retval;
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
		// Dafny.g:184:5: ( ID ':=' 'call' )
		// Dafny.g:184:6: ID ':=' 'call'
		{
		match(input,ID,FOLLOW_ID_in_synpred1_Dafny1030); if (state.failed) return;

		match(input,ASSIGN,FOLLOW_ASSIGN_in_synpred1_Dafny1032); if (state.failed) return;

		match(input,CALL,FOLLOW_CALL_in_synpred1_Dafny1034); if (state.failed) return;

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



	public static final BitSet FOLLOW_LABEL_in_label529 = new BitSet(new long[]{0x0000000002000000L});
	public static final BitSet FOLLOW_ID_in_label532 = new BitSet(new long[]{0x0800000000000000L});
	public static final BitSet FOLLOW_59_in_label534 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_method_in_program548 = new BitSet(new long[]{0x0000004200400002L});
	public static final BitSet FOLLOW_function_in_program552 = new BitSet(new long[]{0x0000004200400002L});
	public static final BitSet FOLLOW_METHOD_in_method571 = new BitSet(new long[]{0x0000000002000000L});
	public static final BitSet FOLLOW_LEMMA_in_method575 = new BitSet(new long[]{0x0000000002000000L});
	public static final BitSet FOLLOW_ID_in_method580 = new BitSet(new long[]{0x0100000000000000L});
	public static final BitSet FOLLOW_56_in_method582 = new BitSet(new long[]{0x0200000002000000L});
	public static final BitSet FOLLOW_vars_in_method584 = new BitSet(new long[]{0x0200000000000000L});
	public static final BitSet FOLLOW_57_in_method587 = new BitSet(new long[]{0x0000500000089000L});
	public static final BitSet FOLLOW_returns__in_method593 = new BitSet(new long[]{0x0000100000089000L});
	public static final BitSet FOLLOW_requires_in_method602 = new BitSet(new long[]{0x0000100000089000L});
	public static final BitSet FOLLOW_ensures_in_method611 = new BitSet(new long[]{0x0000000000089000L});
	public static final BitSet FOLLOW_decreases_in_method620 = new BitSet(new long[]{0x0000000000001000L});
	public static final BitSet FOLLOW_BLOCK_BEGIN_in_method627 = new BitSet(new long[]{0x0060000086002200L});
	public static final BitSet FOLLOW_statements_in_method629 = new BitSet(new long[]{0x0000000000002000L});
	public static final BitSet FOLLOW_BLOCK_END_in_method632 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_FUNCTION_in_function694 = new BitSet(new long[]{0x0000000002000000L});
	public static final BitSet FOLLOW_ID_in_function699 = new BitSet(new long[]{0x0100000000000000L});
	public static final BitSet FOLLOW_56_in_function701 = new BitSet(new long[]{0x0200000002000000L});
	public static final BitSet FOLLOW_vars_in_function704 = new BitSet(new long[]{0x0200000000000000L});
	public static final BitSet FOLLOW_57_in_function707 = new BitSet(new long[]{0x0800000000000000L});
	public static final BitSet FOLLOW_59_in_function710 = new BitSet(new long[]{0x0000800010000080L});
	public static final BitSet FOLLOW_type_in_function713 = new BitSet(new long[]{0x0000000000001000L});
	public static final BitSet FOLLOW_BLOCK_BEGIN_in_function717 = new BitSet(new long[]{0x2100029002001000L});
	public static final BitSet FOLLOW_expression_in_function720 = new BitSet(new long[]{0x0000000000002000L});
	public static final BitSet FOLLOW_BLOCK_END_in_function722 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_var_in_vars735 = new BitSet(new long[]{0x0400000000000002L});
	public static final BitSet FOLLOW_58_in_vars741 = new BitSet(new long[]{0x0000000002000000L});
	public static final BitSet FOLLOW_var_in_vars744 = new BitSet(new long[]{0x0400000000000002L});
	public static final BitSet FOLLOW_ID_in_var759 = new BitSet(new long[]{0x0800000000000000L});
	public static final BitSet FOLLOW_59_in_var761 = new BitSet(new long[]{0x0000800010000080L});
	public static final BitSet FOLLOW_type_in_var763 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_INT_in_type787 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_SET_in_type791 = new BitSet(new long[]{0x0000002000000000L});
	public static final BitSet FOLLOW_LT_in_type794 = new BitSet(new long[]{0x0000000010000000L});
	public static final BitSet FOLLOW_INT_in_type797 = new BitSet(new long[]{0x0000000001000000L});
	public static final BitSet FOLLOW_GT_in_type799 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_ARRAY_in_type806 = new BitSet(new long[]{0x0000002000000000L});
	public static final BitSet FOLLOW_LT_in_type809 = new BitSet(new long[]{0x0000000010000000L});
	public static final BitSet FOLLOW_INT_in_type812 = new BitSet(new long[]{0x0000000001000000L});
	public static final BitSet FOLLOW_GT_in_type814 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_RETURNS_in_returns_827 = new BitSet(new long[]{0x0100000000000000L});
	public static final BitSet FOLLOW_56_in_returns_830 = new BitSet(new long[]{0x0000000002000000L});
	public static final BitSet FOLLOW_vars_in_returns_833 = new BitSet(new long[]{0x0200000000000000L});
	public static final BitSet FOLLOW_57_in_returns_835 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_REQUIRES_in_requires848 = new BitSet(new long[]{0x2100029082001000L});
	public static final BitSet FOLLOW_label_in_requires851 = new BitSet(new long[]{0x2100029002001000L});
	public static final BitSet FOLLOW_expression_in_requires854 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_ENSURES_in_ensures866 = new BitSet(new long[]{0x2100029082001000L});
	public static final BitSet FOLLOW_label_in_ensures869 = new BitSet(new long[]{0x2100029002001000L});
	public static final BitSet FOLLOW_expression_in_ensures872 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_DECREASES_in_decreases884 = new BitSet(new long[]{0x2100029002001000L});
	public static final BitSet FOLLOW_expression_in_decreases887 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_INVARIANT_in_invariant899 = new BitSet(new long[]{0x2100029082001000L});
	public static final BitSet FOLLOW_label_in_invariant902 = new BitSet(new long[]{0x2100029002001000L});
	public static final BitSet FOLLOW_expression_in_invariant905 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_BLOCK_BEGIN_in_block917 = new BitSet(new long[]{0x0060000086002200L});
	public static final BitSet FOLLOW_statements_in_block919 = new BitSet(new long[]{0x0000000000002000L});
	public static final BitSet FOLLOW_BLOCK_END_in_block922 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_block_in_relaxedBlock945 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_statement_in_relaxedBlock951 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_statement_in_statements973 = new BitSet(new long[]{0x0060000086000202L});
	public static final BitSet FOLLOW_VAR_in_statement990 = new BitSet(new long[]{0x0000000002000000L});
	public static final BitSet FOLLOW_ID_in_statement993 = new BitSet(new long[]{0x0800000000000000L});
	public static final BitSet FOLLOW_59_in_statement995 = new BitSet(new long[]{0x0000800010000080L});
	public static final BitSet FOLLOW_type_in_statement998 = new BitSet(new long[]{0x1000000000000400L});
	public static final BitSet FOLLOW_ASSIGN_in_statement1001 = new BitSet(new long[]{0x2100029002001000L});
	public static final BitSet FOLLOW_expression_in_statement1004 = new BitSet(new long[]{0x1000000000000000L});
	public static final BitSet FOLLOW_60_in_statement1008 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_ID_in_statement1015 = new BitSet(new long[]{0x0000000000000400L});
	public static final BitSet FOLLOW_ASSIGN_in_statement1017 = new BitSet(new long[]{0x2100029002001000L});
	public static final BitSet FOLLOW_expression_in_statement1020 = new BitSet(new long[]{0x1000000000000000L});
	public static final BitSet FOLLOW_60_in_statement1022 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_ID_in_statement1041 = new BitSet(new long[]{0x0000000000000400L});
	public static final BitSet FOLLOW_ASSIGN_in_statement1043 = new BitSet(new long[]{0x0000000000004000L});
	public static final BitSet FOLLOW_CALL_in_statement1045 = new BitSet(new long[]{0x0000000002000000L});
	public static final BitSet FOLLOW_ID_in_statement1049 = new BitSet(new long[]{0x0100000000000000L});
	public static final BitSet FOLLOW_56_in_statement1051 = new BitSet(new long[]{0x2300029002001000L});
	public static final BitSet FOLLOW_expressions_in_statement1053 = new BitSet(new long[]{0x0200000000000000L});
	public static final BitSet FOLLOW_57_in_statement1056 = new BitSet(new long[]{0x1000000000000000L});
	public static final BitSet FOLLOW_60_in_statement1058 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_ids_in_statement1095 = new BitSet(new long[]{0x0000000000000400L});
	public static final BitSet FOLLOW_ASSIGN_in_statement1097 = new BitSet(new long[]{0x0000000000004000L});
	public static final BitSet FOLLOW_CALL_in_statement1099 = new BitSet(new long[]{0x0000000002000000L});
	public static final BitSet FOLLOW_ID_in_statement1101 = new BitSet(new long[]{0x0100000000000000L});
	public static final BitSet FOLLOW_56_in_statement1103 = new BitSet(new long[]{0x2300029002001000L});
	public static final BitSet FOLLOW_expressions_in_statement1105 = new BitSet(new long[]{0x0200000000000000L});
	public static final BitSet FOLLOW_57_in_statement1108 = new BitSet(new long[]{0x1000000000000000L});
	public static final BitSet FOLLOW_60_in_statement1110 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_label_in_statement1145 = new BitSet(new long[]{0x0040000000000000L});
	public static final BitSet FOLLOW_WHILE_in_statement1154 = new BitSet(new long[]{0x2100029002001000L});
	public static final BitSet FOLLOW_expression_in_statement1156 = new BitSet(new long[]{0x0000000040000000L});
	public static final BitSet FOLLOW_invariant_in_statement1158 = new BitSet(new long[]{0x0000000040008000L});
	public static final BitSet FOLLOW_decreases_in_statement1161 = new BitSet(new long[]{0x0060000086001200L});
	public static final BitSet FOLLOW_relaxedBlock_in_statement1163 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_label_in_statement1195 = new BitSet(new long[]{0x0000000004000000L});
	public static final BitSet FOLLOW_IF_in_statement1198 = new BitSet(new long[]{0x2100029002001000L});
	public static final BitSet FOLLOW_expression_in_statement1201 = new BitSet(new long[]{0x0060000086001200L});
	public static final BitSet FOLLOW_relaxedBlock_in_statement1203 = new BitSet(new long[]{0x0000000000040002L});
	public static final BitSet FOLLOW_ELSE_in_statement1224 = new BitSet(new long[]{0x0060000086001200L});
	public static final BitSet FOLLOW_relaxedBlock_in_statement1227 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_ASSERT_in_statement1236 = new BitSet(new long[]{0x2100029082001000L});
	public static final BitSet FOLLOW_LABEL_in_statement1241 = new BitSet(new long[]{0x0000000002000000L});
	public static final BitSet FOLLOW_ID_in_statement1244 = new BitSet(new long[]{0x0800000000000000L});
	public static final BitSet FOLLOW_59_in_statement1246 = new BitSet(new long[]{0x2100029002001000L});
	public static final BitSet FOLLOW_expression_in_statement1252 = new BitSet(new long[]{0x1000000000000000L});
	public static final BitSet FOLLOW_60_in_statement1254 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_ID_in_ids1267 = new BitSet(new long[]{0x0400000000000000L});
	public static final BitSet FOLLOW_58_in_ids1270 = new BitSet(new long[]{0x0000000002000000L});
	public static final BitSet FOLLOW_ID_in_ids1273 = new BitSet(new long[]{0x0400000000000002L});
	public static final BitSet FOLLOW_expression_in_expressions1287 = new BitSet(new long[]{0x0400000000000002L});
	public static final BitSet FOLLOW_58_in_expressions1291 = new BitSet(new long[]{0x2100029002001000L});
	public static final BitSet FOLLOW_expression_in_expressions1294 = new BitSet(new long[]{0x0400000000000002L});
	public static final BitSet FOLLOW_or_expr_in_expression1309 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_and_expr_in_or_expr1318 = new BitSet(new long[]{0x0000040008000002L});
	public static final BitSet FOLLOW_OR_in_or_expr1323 = new BitSet(new long[]{0x2100029002001000L});
	public static final BitSet FOLLOW_IMPLIES_in_or_expr1328 = new BitSet(new long[]{0x2100029002001000L});
	public static final BitSet FOLLOW_or_expr_in_or_expr1332 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_rel_expr_in_and_expr1347 = new BitSet(new long[]{0x0000000000000022L});
	public static final BitSet FOLLOW_AND_in_and_expr1351 = new BitSet(new long[]{0x2100029002001000L});
	public static final BitSet FOLLOW_and_expr_in_and_expr1354 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_add_expr_in_rel_expr1369 = new BitSet(new long[]{0x0000002101900002L});
	public static final BitSet FOLLOW_LT_in_rel_expr1374 = new BitSet(new long[]{0x2100029002001000L});
	public static final BitSet FOLLOW_GT_in_rel_expr1379 = new BitSet(new long[]{0x2100029002001000L});
	public static final BitSet FOLLOW_EQ_in_rel_expr1384 = new BitSet(new long[]{0x2100029002001000L});
	public static final BitSet FOLLOW_LE_in_rel_expr1389 = new BitSet(new long[]{0x2100029002001000L});
	public static final BitSet FOLLOW_GE_in_rel_expr1394 = new BitSet(new long[]{0x2100029002001000L});
	public static final BitSet FOLLOW_add_expr_in_rel_expr1398 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_mul_expr_in_add_expr1413 = new BitSet(new long[]{0x0010088000000002L});
	public static final BitSet FOLLOW_set_in_add_expr1417 = new BitSet(new long[]{0x2100029002001000L});
	public static final BitSet FOLLOW_add_expr_in_add_expr1430 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_prefix_expr_in_mul_expr1445 = new BitSet(new long[]{0x0008000020000002L});
	public static final BitSet FOLLOW_set_in_mul_expr1449 = new BitSet(new long[]{0x2100029002001000L});
	public static final BitSet FOLLOW_mul_expr_in_mul_expr1458 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_MINUS_in_prefix_expr1475 = new BitSet(new long[]{0x2100029002001000L});
	public static final BitSet FOLLOW_prefix_expr_in_prefix_expr1478 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_NOT_in_prefix_expr1484 = new BitSet(new long[]{0x2100029002001000L});
	public static final BitSet FOLLOW_prefix_expr_in_prefix_expr1487 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_postfix_expr_in_prefix_expr1493 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_atom_expr_in_postfix_expr1505 = new BitSet(new long[]{0x2000000000010002L});
	public static final BitSet FOLLOW_61_in_postfix_expr1511 = new BitSet(new long[]{0x2100029002001000L});
	public static final BitSet FOLLOW_expression_in_postfix_expr1513 = new BitSet(new long[]{0x4000000000000000L});
	public static final BitSet FOLLOW_62_in_postfix_expr1515 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_DOT_in_postfix_expr1533 = new BitSet(new long[]{0x0000000400000000L});
	public static final BitSet FOLLOW_LENGTH_in_postfix_expr1535 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_EOF_in_postfix_expr1559 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_ID_in_atom_expr1581 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_LIT_in_atom_expr1587 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_quantifier_in_atom_expr1593 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_56_in_atom_expr1599 = new BitSet(new long[]{0x2100029002001000L});
	public static final BitSet FOLLOW_expression_in_atom_expr1602 = new BitSet(new long[]{0x0200000000000000L});
	public static final BitSet FOLLOW_57_in_atom_expr1604 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_BLOCK_BEGIN_in_atom_expr1611 = new BitSet(new long[]{0x2100029002003000L});
	public static final BitSet FOLLOW_expressions_in_atom_expr1613 = new BitSet(new long[]{0x0000000000002000L});
	public static final BitSet FOLLOW_BLOCK_END_in_atom_expr1616 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_61_in_atom_expr1631 = new BitSet(new long[]{0x6100029002001000L});
	public static final BitSet FOLLOW_expressions_in_atom_expr1633 = new BitSet(new long[]{0x4000000000000000L});
	public static final BitSet FOLLOW_62_in_atom_expr1636 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_56_in_quantifier1657 = new BitSet(new long[]{0x0000000000200010L});
	public static final BitSet FOLLOW_ALL_in_quantifier1661 = new BitSet(new long[]{0x0000000002000000L});
	public static final BitSet FOLLOW_EX_in_quantifier1666 = new BitSet(new long[]{0x0000000002000000L});
	public static final BitSet FOLLOW_ID_in_quantifier1670 = new BitSet(new long[]{0x0800000000000000L});
	public static final BitSet FOLLOW_59_in_quantifier1672 = new BitSet(new long[]{0x0000800010000080L});
	public static final BitSet FOLLOW_type_in_quantifier1675 = new BitSet(new long[]{0x0000000000020000L});
	public static final BitSet FOLLOW_DOUBLECOLON_in_quantifier1677 = new BitSet(new long[]{0x2100029002001000L});
	public static final BitSet FOLLOW_expression_in_quantifier1680 = new BitSet(new long[]{0x0200000000000000L});
	public static final BitSet FOLLOW_57_in_quantifier1682 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_ID_in_synpred1_Dafny1030 = new BitSet(new long[]{0x0000000000000400L});
	public static final BitSet FOLLOW_ASSIGN_in_synpred1_Dafny1032 = new BitSet(new long[]{0x0000000000004000L});
	public static final BitSet FOLLOW_CALL_in_synpred1_Dafny1034 = new BitSet(new long[]{0x0000000000000002L});
}
