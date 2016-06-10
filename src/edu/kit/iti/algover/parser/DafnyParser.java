// $ANTLR 3.5.1 Dafny.g 2016-06-10 09:23:39

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
		"ARRAY_ACCESS", "ARRAY_UPDATE", "ASSERT", "ASSIGN", "ASSUME", "BLOCK", 
		"BLOCK_BEGIN", "BLOCK_END", "CALL", "DECREASES", "DOT", "DOUBLECOLON", 
		"ELSE", "ENSURES", "EQ", "EX", "FUNCTION", "GE", "GT", "HAVOC", "ID", 
		"IF", "IMPLIES", "INT", "INTERSECT", "INVARIANT", "LABEL", "LE", "LEMMA", 
		"LENGTH", "LISTEX", "LIT", "LT", "METHOD", "MINUS", "MULTILINE_COMMENT", 
		"NOT", "OR", "PLUS", "REQUIRES", "RESULTS", "RETURNS", "SET", "SETEX", 
		"SINGLELINE_COMMENT", "THEN", "TIMES", "UNION", "VAR", "WHILE", "WS", 
		"'('", "')'", "','", "':'", "';'", "'['", "']'"
	};
	public static final int EOF=-1;
	public static final int T__59=59;
	public static final int T__60=60;
	public static final int T__61=61;
	public static final int T__62=62;
	public static final int T__63=63;
	public static final int T__64=64;
	public static final int T__65=65;
	public static final int ALL=4;
	public static final int AND=5;
	public static final int ARGS=6;
	public static final int ARRAY=7;
	public static final int ARRAY_ACCESS=8;
	public static final int ARRAY_UPDATE=9;
	public static final int ASSERT=10;
	public static final int ASSIGN=11;
	public static final int ASSUME=12;
	public static final int BLOCK=13;
	public static final int BLOCK_BEGIN=14;
	public static final int BLOCK_END=15;
	public static final int CALL=16;
	public static final int DECREASES=17;
	public static final int DOT=18;
	public static final int DOUBLECOLON=19;
	public static final int ELSE=20;
	public static final int ENSURES=21;
	public static final int EQ=22;
	public static final int EX=23;
	public static final int FUNCTION=24;
	public static final int GE=25;
	public static final int GT=26;
	public static final int HAVOC=27;
	public static final int ID=28;
	public static final int IF=29;
	public static final int IMPLIES=30;
	public static final int INT=31;
	public static final int INTERSECT=32;
	public static final int INVARIANT=33;
	public static final int LABEL=34;
	public static final int LE=35;
	public static final int LEMMA=36;
	public static final int LENGTH=37;
	public static final int LISTEX=38;
	public static final int LIT=39;
	public static final int LT=40;
	public static final int METHOD=41;
	public static final int MINUS=42;
	public static final int MULTILINE_COMMENT=43;
	public static final int NOT=44;
	public static final int OR=45;
	public static final int PLUS=46;
	public static final int REQUIRES=47;
	public static final int RESULTS=48;
	public static final int RETURNS=49;
	public static final int SET=50;
	public static final int SETEX=51;
	public static final int SINGLELINE_COMMENT=52;
	public static final int THEN=53;
	public static final int TIMES=54;
	public static final int UNION=55;
	public static final int VAR=56;
	public static final int WHILE=57;
	public static final int WS=58;

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
	// Dafny.g:110:1: label : 'label' ^ ID ':' !;
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
			// Dafny.g:110:6: ( 'label' ^ ID ':' !)
			// Dafny.g:111:3: 'label' ^ ID ':' !
			{
			root_0 = (DafnyTree)adaptor.nil();


			string_literal1=(Token)match(input,LABEL,FOLLOW_LABEL_in_label547); if (state.failed) return retval;
			if ( state.backtracking==0 ) {
			string_literal1_tree = (DafnyTree)adaptor.create(string_literal1);
			root_0 = (DafnyTree)adaptor.becomeRoot(string_literal1_tree, root_0);
			}

			ID2=(Token)match(input,ID,FOLLOW_ID_in_label550); if (state.failed) return retval;
			if ( state.backtracking==0 ) {
			ID2_tree = (DafnyTree)adaptor.create(ID2);
			adaptor.addChild(root_0, ID2_tree);
			}

			char_literal3=(Token)match(input,62,FOLLOW_62_in_label552); if (state.failed) return retval;
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
	// Dafny.g:114:1: program : ( method | function )+ ;
	public final DafnyParser.program_return program() throws RecognitionException {
		DafnyParser.program_return retval = new DafnyParser.program_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		ParserRuleReturnScope method4 =null;
		ParserRuleReturnScope function5 =null;


		try {
			// Dafny.g:114:8: ( ( method | function )+ )
			// Dafny.g:115:3: ( method | function )+
			{
			root_0 = (DafnyTree)adaptor.nil();


			// Dafny.g:115:3: ( method | function )+
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
					// Dafny.g:115:4: method
					{
					pushFollow(FOLLOW_method_in_program566);
					method4=method();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, method4.getTree());

					}
					break;
				case 2 :
					// Dafny.g:115:13: function
					{
					pushFollow(FOLLOW_function_in_program570);
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
	// Dafny.g:118:1: method : tok= ( 'method' | 'lemma' ) ID '(' ( vars )? ')' ( returns_ )? ( requires )* ( ensures )* ( decreases )? '{' ( statements )? '}' -> ^( METHOD[tok] ID ^( ARGS ( vars )? ) ( returns_ )? ( requires )* ( ensures )* ( decreases )? ^( BLOCK ( statements )? ) ) ;
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
		RewriteRuleTokenStream stream_59=new RewriteRuleTokenStream(adaptor,"token 59");
		RewriteRuleTokenStream stream_ID=new RewriteRuleTokenStream(adaptor,"token ID");
		RewriteRuleTokenStream stream_BLOCK_BEGIN=new RewriteRuleTokenStream(adaptor,"token BLOCK_BEGIN");
		RewriteRuleTokenStream stream_LEMMA=new RewriteRuleTokenStream(adaptor,"token LEMMA");
		RewriteRuleTokenStream stream_METHOD=new RewriteRuleTokenStream(adaptor,"token METHOD");
		RewriteRuleTokenStream stream_60=new RewriteRuleTokenStream(adaptor,"token 60");
		RewriteRuleTokenStream stream_BLOCK_END=new RewriteRuleTokenStream(adaptor,"token BLOCK_END");
		RewriteRuleSubtreeStream stream_returns_=new RewriteRuleSubtreeStream(adaptor,"rule returns_");
		RewriteRuleSubtreeStream stream_ensures=new RewriteRuleSubtreeStream(adaptor,"rule ensures");
		RewriteRuleSubtreeStream stream_vars=new RewriteRuleSubtreeStream(adaptor,"rule vars");
		RewriteRuleSubtreeStream stream_decreases=new RewriteRuleSubtreeStream(adaptor,"rule decreases");
		RewriteRuleSubtreeStream stream_statements=new RewriteRuleSubtreeStream(adaptor,"rule statements");
		RewriteRuleSubtreeStream stream_requires=new RewriteRuleSubtreeStream(adaptor,"rule requires");

		try {
			// Dafny.g:118:7: (tok= ( 'method' | 'lemma' ) ID '(' ( vars )? ')' ( returns_ )? ( requires )* ( ensures )* ( decreases )? '{' ( statements )? '}' -> ^( METHOD[tok] ID ^( ARGS ( vars )? ) ( returns_ )? ( requires )* ( ensures )* ( decreases )? ^( BLOCK ( statements )? ) ) )
			// Dafny.g:119:3: tok= ( 'method' | 'lemma' ) ID '(' ( vars )? ')' ( returns_ )? ( requires )* ( ensures )* ( decreases )? '{' ( statements )? '}'
			{
			// Dafny.g:119:9: ( 'method' | 'lemma' )
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
					// Dafny.g:119:10: 'method'
					{
					tok=(Token)match(input,METHOD,FOLLOW_METHOD_in_method589); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_METHOD.add(tok);

					}
					break;
				case 2 :
					// Dafny.g:119:21: 'lemma'
					{
					tok=(Token)match(input,LEMMA,FOLLOW_LEMMA_in_method593); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_LEMMA.add(tok);

					}
					break;

			}

			ID6=(Token)match(input,ID,FOLLOW_ID_in_method598); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_ID.add(ID6);

			char_literal7=(Token)match(input,59,FOLLOW_59_in_method600); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_59.add(char_literal7);

			// Dafny.g:120:10: ( vars )?
			int alt3=2;
			int LA3_0 = input.LA(1);
			if ( (LA3_0==ID) ) {
				alt3=1;
			}
			switch (alt3) {
				case 1 :
					// Dafny.g:120:10: vars
					{
					pushFollow(FOLLOW_vars_in_method602);
					vars8=vars();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_vars.add(vars8.getTree());
					}
					break;

			}

			char_literal9=(Token)match(input,60,FOLLOW_60_in_method605); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_60.add(char_literal9);

			// Dafny.g:121:3: ( returns_ )?
			int alt4=2;
			int LA4_0 = input.LA(1);
			if ( (LA4_0==RETURNS) ) {
				alt4=1;
			}
			switch (alt4) {
				case 1 :
					// Dafny.g:121:5: returns_
					{
					pushFollow(FOLLOW_returns__in_method611);
					returns_10=returns_();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_returns_.add(returns_10.getTree());
					}
					break;

			}

			// Dafny.g:122:3: ( requires )*
			loop5:
			while (true) {
				int alt5=2;
				int LA5_0 = input.LA(1);
				if ( (LA5_0==REQUIRES) ) {
					alt5=1;
				}

				switch (alt5) {
				case 1 :
					// Dafny.g:122:5: requires
					{
					pushFollow(FOLLOW_requires_in_method620);
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

			// Dafny.g:123:3: ( ensures )*
			loop6:
			while (true) {
				int alt6=2;
				int LA6_0 = input.LA(1);
				if ( (LA6_0==ENSURES) ) {
					alt6=1;
				}

				switch (alt6) {
				case 1 :
					// Dafny.g:123:5: ensures
					{
					pushFollow(FOLLOW_ensures_in_method629);
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

			// Dafny.g:124:3: ( decreases )?
			int alt7=2;
			int LA7_0 = input.LA(1);
			if ( (LA7_0==DECREASES) ) {
				alt7=1;
			}
			switch (alt7) {
				case 1 :
					// Dafny.g:124:5: decreases
					{
					pushFollow(FOLLOW_decreases_in_method638);
					decreases13=decreases();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_decreases.add(decreases13.getTree());
					}
					break;

			}

			char_literal14=(Token)match(input,BLOCK_BEGIN,FOLLOW_BLOCK_BEGIN_in_method645); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_BLOCK_BEGIN.add(char_literal14);

			// Dafny.g:125:7: ( statements )?
			int alt8=2;
			int LA8_0 = input.LA(1);
			if ( (LA8_0==ASSERT||LA8_0==ASSUME||(LA8_0 >= ID && LA8_0 <= IF)||LA8_0==LABEL||(LA8_0 >= VAR && LA8_0 <= WHILE)) ) {
				alt8=1;
			}
			switch (alt8) {
				case 1 :
					// Dafny.g:125:7: statements
					{
					pushFollow(FOLLOW_statements_in_method647);
					statements15=statements();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_statements.add(statements15.getTree());
					}
					break;

			}

			char_literal16=(Token)match(input,BLOCK_END,FOLLOW_BLOCK_END_in_method650); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_BLOCK_END.add(char_literal16);

			// AST REWRITE
			// elements: requires, statements, returns_, ensures, vars, decreases, ID
			// token labels: 
			// rule labels: retval
			// token list labels: 
			// rule list labels: 
			// wildcard labels: 
			if ( state.backtracking==0 ) {
			retval.tree = root_0;
			RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

			root_0 = (DafnyTree)adaptor.nil();
			// 126:3: -> ^( METHOD[tok] ID ^( ARGS ( vars )? ) ( returns_ )? ( requires )* ( ensures )* ( decreases )? ^( BLOCK ( statements )? ) )
			{
				// Dafny.g:127:5: ^( METHOD[tok] ID ^( ARGS ( vars )? ) ( returns_ )? ( requires )* ( ensures )* ( decreases )? ^( BLOCK ( statements )? ) )
				{
				DafnyTree root_1 = (DafnyTree)adaptor.nil();
				root_1 = (DafnyTree)adaptor.becomeRoot((DafnyTree)adaptor.create(METHOD, tok), root_1);
				adaptor.addChild(root_1, stream_ID.nextNode());
				// Dafny.g:127:22: ^( ARGS ( vars )? )
				{
				DafnyTree root_2 = (DafnyTree)adaptor.nil();
				root_2 = (DafnyTree)adaptor.becomeRoot((DafnyTree)adaptor.create(ARGS, "ARGS"), root_2);
				// Dafny.g:127:29: ( vars )?
				if ( stream_vars.hasNext() ) {
					adaptor.addChild(root_2, stream_vars.nextTree());
				}
				stream_vars.reset();

				adaptor.addChild(root_1, root_2);
				}

				// Dafny.g:127:36: ( returns_ )?
				if ( stream_returns_.hasNext() ) {
					adaptor.addChild(root_1, stream_returns_.nextTree());
				}
				stream_returns_.reset();

				// Dafny.g:127:46: ( requires )*
				while ( stream_requires.hasNext() ) {
					adaptor.addChild(root_1, stream_requires.nextTree());
				}
				stream_requires.reset();

				// Dafny.g:127:56: ( ensures )*
				while ( stream_ensures.hasNext() ) {
					adaptor.addChild(root_1, stream_ensures.nextTree());
				}
				stream_ensures.reset();

				// Dafny.g:128:9: ( decreases )?
				if ( stream_decreases.hasNext() ) {
					adaptor.addChild(root_1, stream_decreases.nextTree());
				}
				stream_decreases.reset();

				// Dafny.g:128:20: ^( BLOCK ( statements )? )
				{
				DafnyTree root_2 = (DafnyTree)adaptor.nil();
				root_2 = (DafnyTree)adaptor.becomeRoot((DafnyTree)adaptor.create(BLOCK, "BLOCK"), root_2);
				// Dafny.g:128:28: ( statements )?
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
	// Dafny.g:131:1: function : 'function' ^ ID '(' ! ( vars )? ')' ! ':' ! type '{' ! expression '}' !;
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
			// Dafny.g:131:9: ( 'function' ^ ID '(' ! ( vars )? ')' ! ':' ! type '{' ! expression '}' !)
			// Dafny.g:132:3: 'function' ^ ID '(' ! ( vars )? ')' ! ':' ! type '{' ! expression '}' !
			{
			root_0 = (DafnyTree)adaptor.nil();


			string_literal17=(Token)match(input,FUNCTION,FOLLOW_FUNCTION_in_function712); if (state.failed) return retval;
			if ( state.backtracking==0 ) {
			string_literal17_tree = (DafnyTree)adaptor.create(string_literal17);
			root_0 = (DafnyTree)adaptor.becomeRoot(string_literal17_tree, root_0);
			}

			ID18=(Token)match(input,ID,FOLLOW_ID_in_function717); if (state.failed) return retval;
			if ( state.backtracking==0 ) {
			ID18_tree = (DafnyTree)adaptor.create(ID18);
			adaptor.addChild(root_0, ID18_tree);
			}

			char_literal19=(Token)match(input,59,FOLLOW_59_in_function719); if (state.failed) return retval;
			// Dafny.g:133:11: ( vars )?
			int alt9=2;
			int LA9_0 = input.LA(1);
			if ( (LA9_0==ID) ) {
				alt9=1;
			}
			switch (alt9) {
				case 1 :
					// Dafny.g:133:11: vars
					{
					pushFollow(FOLLOW_vars_in_function722);
					vars20=vars();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, vars20.getTree());

					}
					break;

			}

			char_literal21=(Token)match(input,60,FOLLOW_60_in_function725); if (state.failed) return retval;
			char_literal22=(Token)match(input,62,FOLLOW_62_in_function728); if (state.failed) return retval;
			pushFollow(FOLLOW_type_in_function731);
			type23=type();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, type23.getTree());

			char_literal24=(Token)match(input,BLOCK_BEGIN,FOLLOW_BLOCK_BEGIN_in_function735); if (state.failed) return retval;
			pushFollow(FOLLOW_expression_in_function738);
			expression25=expression();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, expression25.getTree());

			char_literal26=(Token)match(input,BLOCK_END,FOLLOW_BLOCK_END_in_function740); if (state.failed) return retval;
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
	// Dafny.g:137:1: vars : var ( ',' ! var )* ;
	public final DafnyParser.vars_return vars() throws RecognitionException {
		DafnyParser.vars_return retval = new DafnyParser.vars_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		Token char_literal28=null;
		ParserRuleReturnScope var27 =null;
		ParserRuleReturnScope var29 =null;

		DafnyTree char_literal28_tree=null;

		try {
			// Dafny.g:137:5: ( var ( ',' ! var )* )
			// Dafny.g:138:3: var ( ',' ! var )*
			{
			root_0 = (DafnyTree)adaptor.nil();


			pushFollow(FOLLOW_var_in_vars753);
			var27=var();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, var27.getTree());

			// Dafny.g:139:3: ( ',' ! var )*
			loop10:
			while (true) {
				int alt10=2;
				int LA10_0 = input.LA(1);
				if ( (LA10_0==61) ) {
					alt10=1;
				}

				switch (alt10) {
				case 1 :
					// Dafny.g:139:5: ',' ! var
					{
					char_literal28=(Token)match(input,61,FOLLOW_61_in_vars759); if (state.failed) return retval;
					pushFollow(FOLLOW_var_in_vars762);
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
	// Dafny.g:142:1: var : ID ':' type -> ^( VAR ID type ) ;
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
		RewriteRuleTokenStream stream_62=new RewriteRuleTokenStream(adaptor,"token 62");
		RewriteRuleSubtreeStream stream_type=new RewriteRuleSubtreeStream(adaptor,"rule type");

		try {
			// Dafny.g:142:4: ( ID ':' type -> ^( VAR ID type ) )
			// Dafny.g:143:3: ID ':' type
			{
			ID30=(Token)match(input,ID,FOLLOW_ID_in_var777); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_ID.add(ID30);

			char_literal31=(Token)match(input,62,FOLLOW_62_in_var779); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_62.add(char_literal31);

			pushFollow(FOLLOW_type_in_var781);
			type32=type();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) stream_type.add(type32.getTree());
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

			root_0 = (DafnyTree)adaptor.nil();
			// 143:15: -> ^( VAR ID type )
			{
				// Dafny.g:143:18: ^( VAR ID type )
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
	// Dafny.g:146:1: type : ( INT | SET ^ '<' ! INT '>' !| ARRAY ^ '<' ! INT '>' !);
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
			// Dafny.g:146:5: ( INT | SET ^ '<' ! INT '>' !| ARRAY ^ '<' ! INT '>' !)
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
					// Dafny.g:147:5: INT
					{
					root_0 = (DafnyTree)adaptor.nil();


					INT33=(Token)match(input,INT,FOLLOW_INT_in_type805); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					INT33_tree = (DafnyTree)adaptor.create(INT33);
					adaptor.addChild(root_0, INT33_tree);
					}

					}
					break;
				case 2 :
					// Dafny.g:147:11: SET ^ '<' ! INT '>' !
					{
					root_0 = (DafnyTree)adaptor.nil();


					SET34=(Token)match(input,SET,FOLLOW_SET_in_type809); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					SET34_tree = (DafnyTree)adaptor.create(SET34);
					root_0 = (DafnyTree)adaptor.becomeRoot(SET34_tree, root_0);
					}

					char_literal35=(Token)match(input,LT,FOLLOW_LT_in_type812); if (state.failed) return retval;
					INT36=(Token)match(input,INT,FOLLOW_INT_in_type815); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					INT36_tree = (DafnyTree)adaptor.create(INT36);
					adaptor.addChild(root_0, INT36_tree);
					}

					char_literal37=(Token)match(input,GT,FOLLOW_GT_in_type817); if (state.failed) return retval;
					}
					break;
				case 3 :
					// Dafny.g:148:5: ARRAY ^ '<' ! INT '>' !
					{
					root_0 = (DafnyTree)adaptor.nil();


					ARRAY38=(Token)match(input,ARRAY,FOLLOW_ARRAY_in_type824); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					ARRAY38_tree = (DafnyTree)adaptor.create(ARRAY38);
					root_0 = (DafnyTree)adaptor.becomeRoot(ARRAY38_tree, root_0);
					}

					char_literal39=(Token)match(input,LT,FOLLOW_LT_in_type827); if (state.failed) return retval;
					INT40=(Token)match(input,INT,FOLLOW_INT_in_type830); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					INT40_tree = (DafnyTree)adaptor.create(INT40);
					adaptor.addChild(root_0, INT40_tree);
					}

					char_literal41=(Token)match(input,GT,FOLLOW_GT_in_type832); if (state.failed) return retval;
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
	// Dafny.g:151:1: returns_ : RETURNS ^ '(' ! vars ')' !;
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
			// Dafny.g:151:9: ( RETURNS ^ '(' ! vars ')' !)
			// Dafny.g:152:3: RETURNS ^ '(' ! vars ')' !
			{
			root_0 = (DafnyTree)adaptor.nil();


			RETURNS42=(Token)match(input,RETURNS,FOLLOW_RETURNS_in_returns_845); if (state.failed) return retval;
			if ( state.backtracking==0 ) {
			RETURNS42_tree = (DafnyTree)adaptor.create(RETURNS42);
			root_0 = (DafnyTree)adaptor.becomeRoot(RETURNS42_tree, root_0);
			}

			char_literal43=(Token)match(input,59,FOLLOW_59_in_returns_848); if (state.failed) return retval;
			pushFollow(FOLLOW_vars_in_returns_851);
			vars44=vars();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, vars44.getTree());

			char_literal45=(Token)match(input,60,FOLLOW_60_in_returns_853); if (state.failed) return retval;
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
	// Dafny.g:155:1: requires : REQUIRES ^ ( label )? expression ;
	public final DafnyParser.requires_return requires() throws RecognitionException {
		DafnyParser.requires_return retval = new DafnyParser.requires_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		Token REQUIRES46=null;
		ParserRuleReturnScope label47 =null;
		ParserRuleReturnScope expression48 =null;

		DafnyTree REQUIRES46_tree=null;

		try {
			// Dafny.g:155:9: ( REQUIRES ^ ( label )? expression )
			// Dafny.g:156:3: REQUIRES ^ ( label )? expression
			{
			root_0 = (DafnyTree)adaptor.nil();


			REQUIRES46=(Token)match(input,REQUIRES,FOLLOW_REQUIRES_in_requires866); if (state.failed) return retval;
			if ( state.backtracking==0 ) {
			REQUIRES46_tree = (DafnyTree)adaptor.create(REQUIRES46);
			root_0 = (DafnyTree)adaptor.becomeRoot(REQUIRES46_tree, root_0);
			}

			// Dafny.g:156:13: ( label )?
			int alt12=2;
			int LA12_0 = input.LA(1);
			if ( (LA12_0==LABEL) ) {
				alt12=1;
			}
			switch (alt12) {
				case 1 :
					// Dafny.g:156:13: label
					{
					pushFollow(FOLLOW_label_in_requires869);
					label47=label();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, label47.getTree());

					}
					break;

			}

			pushFollow(FOLLOW_expression_in_requires872);
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
	// Dafny.g:159:1: ensures : ENSURES ^ ( label )? expression ;
	public final DafnyParser.ensures_return ensures() throws RecognitionException {
		DafnyParser.ensures_return retval = new DafnyParser.ensures_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		Token ENSURES49=null;
		ParserRuleReturnScope label50 =null;
		ParserRuleReturnScope expression51 =null;

		DafnyTree ENSURES49_tree=null;

		try {
			// Dafny.g:159:8: ( ENSURES ^ ( label )? expression )
			// Dafny.g:160:3: ENSURES ^ ( label )? expression
			{
			root_0 = (DafnyTree)adaptor.nil();


			ENSURES49=(Token)match(input,ENSURES,FOLLOW_ENSURES_in_ensures884); if (state.failed) return retval;
			if ( state.backtracking==0 ) {
			ENSURES49_tree = (DafnyTree)adaptor.create(ENSURES49);
			root_0 = (DafnyTree)adaptor.becomeRoot(ENSURES49_tree, root_0);
			}

			// Dafny.g:160:12: ( label )?
			int alt13=2;
			int LA13_0 = input.LA(1);
			if ( (LA13_0==LABEL) ) {
				alt13=1;
			}
			switch (alt13) {
				case 1 :
					// Dafny.g:160:12: label
					{
					pushFollow(FOLLOW_label_in_ensures887);
					label50=label();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, label50.getTree());

					}
					break;

			}

			pushFollow(FOLLOW_expression_in_ensures890);
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
	// Dafny.g:163:1: decreases : DECREASES ^ expression ;
	public final DafnyParser.decreases_return decreases() throws RecognitionException {
		DafnyParser.decreases_return retval = new DafnyParser.decreases_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		Token DECREASES52=null;
		ParserRuleReturnScope expression53 =null;

		DafnyTree DECREASES52_tree=null;

		try {
			// Dafny.g:163:10: ( DECREASES ^ expression )
			// Dafny.g:164:3: DECREASES ^ expression
			{
			root_0 = (DafnyTree)adaptor.nil();


			DECREASES52=(Token)match(input,DECREASES,FOLLOW_DECREASES_in_decreases902); if (state.failed) return retval;
			if ( state.backtracking==0 ) {
			DECREASES52_tree = (DafnyTree)adaptor.create(DECREASES52);
			root_0 = (DafnyTree)adaptor.becomeRoot(DECREASES52_tree, root_0);
			}

			pushFollow(FOLLOW_expression_in_decreases905);
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
	// Dafny.g:167:1: invariant : INVARIANT ^ ( label )? expression ;
	public final DafnyParser.invariant_return invariant() throws RecognitionException {
		DafnyParser.invariant_return retval = new DafnyParser.invariant_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		Token INVARIANT54=null;
		ParserRuleReturnScope label55 =null;
		ParserRuleReturnScope expression56 =null;

		DafnyTree INVARIANT54_tree=null;

		try {
			// Dafny.g:167:10: ( INVARIANT ^ ( label )? expression )
			// Dafny.g:168:3: INVARIANT ^ ( label )? expression
			{
			root_0 = (DafnyTree)adaptor.nil();


			INVARIANT54=(Token)match(input,INVARIANT,FOLLOW_INVARIANT_in_invariant917); if (state.failed) return retval;
			if ( state.backtracking==0 ) {
			INVARIANT54_tree = (DafnyTree)adaptor.create(INVARIANT54);
			root_0 = (DafnyTree)adaptor.becomeRoot(INVARIANT54_tree, root_0);
			}

			// Dafny.g:168:14: ( label )?
			int alt14=2;
			int LA14_0 = input.LA(1);
			if ( (LA14_0==LABEL) ) {
				alt14=1;
			}
			switch (alt14) {
				case 1 :
					// Dafny.g:168:14: label
					{
					pushFollow(FOLLOW_label_in_invariant920);
					label55=label();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, label55.getTree());

					}
					break;

			}

			pushFollow(FOLLOW_expression_in_invariant923);
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
	// Dafny.g:171:1: block : '{' ( statements )? '}' -> ^( BLOCK ( statements )? ) ;
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
			// Dafny.g:171:6: ( '{' ( statements )? '}' -> ^( BLOCK ( statements )? ) )
			// Dafny.g:172:3: '{' ( statements )? '}'
			{
			char_literal57=(Token)match(input,BLOCK_BEGIN,FOLLOW_BLOCK_BEGIN_in_block935); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_BLOCK_BEGIN.add(char_literal57);

			// Dafny.g:172:7: ( statements )?
			int alt15=2;
			int LA15_0 = input.LA(1);
			if ( (LA15_0==ASSERT||LA15_0==ASSUME||(LA15_0 >= ID && LA15_0 <= IF)||LA15_0==LABEL||(LA15_0 >= VAR && LA15_0 <= WHILE)) ) {
				alt15=1;
			}
			switch (alt15) {
				case 1 :
					// Dafny.g:172:7: statements
					{
					pushFollow(FOLLOW_statements_in_block937);
					statements58=statements();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_statements.add(statements58.getTree());
					}
					break;

			}

			char_literal59=(Token)match(input,BLOCK_END,FOLLOW_BLOCK_END_in_block940); if (state.failed) return retval; 
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
			// 172:23: -> ^( BLOCK ( statements )? )
			{
				// Dafny.g:172:26: ^( BLOCK ( statements )? )
				{
				DafnyTree root_1 = (DafnyTree)adaptor.nil();
				root_1 = (DafnyTree)adaptor.becomeRoot((DafnyTree)adaptor.create(BLOCK, "BLOCK"), root_1);
				// Dafny.g:172:34: ( statements )?
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
	// Dafny.g:175:1: relaxedBlock : ( block | statement -> ^( BLOCK statement ) );
	public final DafnyParser.relaxedBlock_return relaxedBlock() throws RecognitionException {
		DafnyParser.relaxedBlock_return retval = new DafnyParser.relaxedBlock_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		ParserRuleReturnScope block60 =null;
		ParserRuleReturnScope statement61 =null;

		RewriteRuleSubtreeStream stream_statement=new RewriteRuleSubtreeStream(adaptor,"rule statement");

		try {
			// Dafny.g:175:13: ( block | statement -> ^( BLOCK statement ) )
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
					// Dafny.g:176:5: block
					{
					root_0 = (DafnyTree)adaptor.nil();


					pushFollow(FOLLOW_block_in_relaxedBlock963);
					block60=block();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, block60.getTree());

					}
					break;
				case 2 :
					// Dafny.g:177:5: statement
					{
					pushFollow(FOLLOW_statement_in_relaxedBlock969);
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
					// 177:15: -> ^( BLOCK statement )
					{
						// Dafny.g:177:18: ^( BLOCK statement )
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
	// Dafny.g:180:1: statements : ( statement )+ ;
	public final DafnyParser.statements_return statements() throws RecognitionException {
		DafnyParser.statements_return retval = new DafnyParser.statements_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		ParserRuleReturnScope statement62 =null;


		try {
			// Dafny.g:180:11: ( ( statement )+ )
			// Dafny.g:181:3: ( statement )+
			{
			root_0 = (DafnyTree)adaptor.nil();


			// Dafny.g:181:3: ( statement )+
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
					// Dafny.g:181:5: statement
					{
					pushFollow(FOLLOW_statement_in_statements991);
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
	// Dafny.g:184:1: statement : ( VAR ^ ID ':' ! type ( ':=' ! expression )? ';' !| ID ':=' '*' ';' -> ^( HAVOC ID ) | ID ':=' ^ expression ';' !| ID '[' i= expression ']' ass= ':=' v= expression ';' -> ^( ARRAY_UPDATE[$ass] ID $i $v) | ( ID ':=' 'call' )=>r= ID ':=' 'call' f= ID '(' ( expressions )? ')' ';' -> ^( 'call' $f ^( RESULTS $r) ^( ARGS ( expressions )? ) ) | ids ':=' 'call' ID '(' ( expressions )? ')' ';' -> ^( 'call' ID ^( RESULTS ids ) ^( ARGS ( expressions )? ) ) | ( label )? 'while' expression ( invariant )+ decreases relaxedBlock -> ^( 'while' ( label )? expression ( invariant )+ decreases relaxedBlock ) | ( label )? 'if' ^ expression relaxedBlock ( options {greedy=true; } : 'else' ! relaxedBlock )? | 'assert' ^ ( 'label' ! ID ':' !)? expression ';' !| 'assume' ^ ( 'label' ! ID ':' !)? expression ';' !);
	public final DafnyParser.statement_return statement() throws RecognitionException {
		DafnyParser.statement_return retval = new DafnyParser.statement_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		Token ass=null;
		Token r=null;
		Token f=null;
		Token VAR63=null;
		Token ID64=null;
		Token char_literal65=null;
		Token string_literal67=null;
		Token char_literal69=null;
		Token ID70=null;
		Token string_literal71=null;
		Token char_literal72=null;
		Token char_literal73=null;
		Token ID74=null;
		Token string_literal75=null;
		Token char_literal77=null;
		Token ID78=null;
		Token char_literal79=null;
		Token char_literal80=null;
		Token char_literal81=null;
		Token string_literal82=null;
		Token string_literal83=null;
		Token char_literal84=null;
		Token char_literal86=null;
		Token char_literal87=null;
		Token string_literal89=null;
		Token string_literal90=null;
		Token ID91=null;
		Token char_literal92=null;
		Token char_literal94=null;
		Token char_literal95=null;
		Token string_literal97=null;
		Token string_literal103=null;
		Token string_literal106=null;
		Token string_literal108=null;
		Token string_literal109=null;
		Token ID110=null;
		Token char_literal111=null;
		Token char_literal113=null;
		Token string_literal114=null;
		Token string_literal115=null;
		Token ID116=null;
		Token char_literal117=null;
		Token char_literal119=null;
		ParserRuleReturnScope i =null;
		ParserRuleReturnScope v =null;
		ParserRuleReturnScope type66 =null;
		ParserRuleReturnScope expression68 =null;
		ParserRuleReturnScope expression76 =null;
		ParserRuleReturnScope expressions85 =null;
		ParserRuleReturnScope ids88 =null;
		ParserRuleReturnScope expressions93 =null;
		ParserRuleReturnScope label96 =null;
		ParserRuleReturnScope expression98 =null;
		ParserRuleReturnScope invariant99 =null;
		ParserRuleReturnScope decreases100 =null;
		ParserRuleReturnScope relaxedBlock101 =null;
		ParserRuleReturnScope label102 =null;
		ParserRuleReturnScope expression104 =null;
		ParserRuleReturnScope relaxedBlock105 =null;
		ParserRuleReturnScope relaxedBlock107 =null;
		ParserRuleReturnScope expression112 =null;
		ParserRuleReturnScope expression118 =null;

		DafnyTree ass_tree=null;
		DafnyTree r_tree=null;
		DafnyTree f_tree=null;
		DafnyTree VAR63_tree=null;
		DafnyTree ID64_tree=null;
		DafnyTree char_literal65_tree=null;
		DafnyTree string_literal67_tree=null;
		DafnyTree char_literal69_tree=null;
		DafnyTree ID70_tree=null;
		DafnyTree string_literal71_tree=null;
		DafnyTree char_literal72_tree=null;
		DafnyTree char_literal73_tree=null;
		DafnyTree ID74_tree=null;
		DafnyTree string_literal75_tree=null;
		DafnyTree char_literal77_tree=null;
		DafnyTree ID78_tree=null;
		DafnyTree char_literal79_tree=null;
		DafnyTree char_literal80_tree=null;
		DafnyTree char_literal81_tree=null;
		DafnyTree string_literal82_tree=null;
		DafnyTree string_literal83_tree=null;
		DafnyTree char_literal84_tree=null;
		DafnyTree char_literal86_tree=null;
		DafnyTree char_literal87_tree=null;
		DafnyTree string_literal89_tree=null;
		DafnyTree string_literal90_tree=null;
		DafnyTree ID91_tree=null;
		DafnyTree char_literal92_tree=null;
		DafnyTree char_literal94_tree=null;
		DafnyTree char_literal95_tree=null;
		DafnyTree string_literal97_tree=null;
		DafnyTree string_literal103_tree=null;
		DafnyTree string_literal106_tree=null;
		DafnyTree string_literal108_tree=null;
		DafnyTree string_literal109_tree=null;
		DafnyTree ID110_tree=null;
		DafnyTree char_literal111_tree=null;
		DafnyTree char_literal113_tree=null;
		DafnyTree string_literal114_tree=null;
		DafnyTree string_literal115_tree=null;
		DafnyTree ID116_tree=null;
		DafnyTree char_literal117_tree=null;
		DafnyTree char_literal119_tree=null;
		RewriteRuleTokenStream stream_59=new RewriteRuleTokenStream(adaptor,"token 59");
		RewriteRuleTokenStream stream_CALL=new RewriteRuleTokenStream(adaptor,"token CALL");
		RewriteRuleTokenStream stream_WHILE=new RewriteRuleTokenStream(adaptor,"token WHILE");
		RewriteRuleTokenStream stream_64=new RewriteRuleTokenStream(adaptor,"token 64");
		RewriteRuleTokenStream stream_ID=new RewriteRuleTokenStream(adaptor,"token ID");
		RewriteRuleTokenStream stream_TIMES=new RewriteRuleTokenStream(adaptor,"token TIMES");
		RewriteRuleTokenStream stream_65=new RewriteRuleTokenStream(adaptor,"token 65");
		RewriteRuleTokenStream stream_63=new RewriteRuleTokenStream(adaptor,"token 63");
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
			// Dafny.g:184:10: ( VAR ^ ID ':' ! type ( ':=' ! expression )? ';' !| ID ':=' '*' ';' -> ^( HAVOC ID ) | ID ':=' ^ expression ';' !| ID '[' i= expression ']' ass= ':=' v= expression ';' -> ^( ARRAY_UPDATE[$ass] ID $i $v) | ( ID ':=' 'call' )=>r= ID ':=' 'call' f= ID '(' ( expressions )? ')' ';' -> ^( 'call' $f ^( RESULTS $r) ^( ARGS ( expressions )? ) ) | ids ':=' 'call' ID '(' ( expressions )? ')' ';' -> ^( 'call' ID ^( RESULTS ids ) ^( ARGS ( expressions )? ) ) | ( label )? 'while' expression ( invariant )+ decreases relaxedBlock -> ^( 'while' ( label )? expression ( invariant )+ decreases relaxedBlock ) | ( label )? 'if' ^ expression relaxedBlock ( options {greedy=true; } : 'else' ! relaxedBlock )? | 'assert' ^ ( 'label' ! ID ':' !)? expression ';' !| 'assume' ^ ( 'label' ! ID ':' !)? expression ';' !)
			int alt27=10;
			switch ( input.LA(1) ) {
			case VAR:
				{
				alt27=1;
				}
				break;
			case ID:
				{
				switch ( input.LA(2) ) {
				case ASSIGN:
					{
					int LA27_8 = input.LA(3);
					if ( (LA27_8==TIMES) ) {
						alt27=2;
					}
					else if ( (LA27_8==CALL) && (synpred1_Dafny())) {
						alt27=5;
					}
					else if ( (LA27_8==BLOCK_BEGIN||LA27_8==ID||LA27_8==LIT||LA27_8==MINUS||LA27_8==NOT||LA27_8==59||LA27_8==64) ) {
						alt27=3;
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
					break;
				case 64:
					{
					alt27=4;
					}
					break;
				case 61:
					{
					alt27=6;
					}
					break;
				default:
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
					int LA27_11 = input.LA(3);
					if ( (LA27_11==62) ) {
						int LA27_15 = input.LA(4);
						if ( (LA27_15==WHILE) ) {
							alt27=7;
						}
						else if ( (LA27_15==IF) ) {
							alt27=8;
						}

						else {
							if (state.backtracking>0) {state.failed=true; return retval;}
							int nvaeMark = input.mark();
							try {
								for (int nvaeConsume = 0; nvaeConsume < 4 - 1; nvaeConsume++) {
									input.consume();
								}
								NoViableAltException nvae =
									new NoViableAltException("", 27, 15, input);
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
								new NoViableAltException("", 27, 11, input);
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
				alt27=7;
				}
				break;
			case IF:
				{
				alt27=8;
				}
				break;
			case ASSERT:
				{
				alt27=9;
				}
				break;
			case ASSUME:
				{
				alt27=10;
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
					// Dafny.g:185:5: VAR ^ ID ':' ! type ( ':=' ! expression )? ';' !
					{
					root_0 = (DafnyTree)adaptor.nil();


					VAR63=(Token)match(input,VAR,FOLLOW_VAR_in_statement1008); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					VAR63_tree = (DafnyTree)adaptor.create(VAR63);
					root_0 = (DafnyTree)adaptor.becomeRoot(VAR63_tree, root_0);
					}

					ID64=(Token)match(input,ID,FOLLOW_ID_in_statement1011); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					ID64_tree = (DafnyTree)adaptor.create(ID64);
					adaptor.addChild(root_0, ID64_tree);
					}

					char_literal65=(Token)match(input,62,FOLLOW_62_in_statement1013); if (state.failed) return retval;
					pushFollow(FOLLOW_type_in_statement1016);
					type66=type();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, type66.getTree());

					// Dafny.g:185:23: ( ':=' ! expression )?
					int alt18=2;
					int LA18_0 = input.LA(1);
					if ( (LA18_0==ASSIGN) ) {
						alt18=1;
					}
					switch (alt18) {
						case 1 :
							// Dafny.g:185:24: ':=' ! expression
							{
							string_literal67=(Token)match(input,ASSIGN,FOLLOW_ASSIGN_in_statement1019); if (state.failed) return retval;
							pushFollow(FOLLOW_expression_in_statement1022);
							expression68=expression();
							state._fsp--;
							if (state.failed) return retval;
							if ( state.backtracking==0 ) adaptor.addChild(root_0, expression68.getTree());

							}
							break;

					}

					char_literal69=(Token)match(input,63,FOLLOW_63_in_statement1026); if (state.failed) return retval;
					}
					break;
				case 2 :
					// Dafny.g:186:5: ID ':=' '*' ';'
					{
					ID70=(Token)match(input,ID,FOLLOW_ID_in_statement1033); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_ID.add(ID70);

					string_literal71=(Token)match(input,ASSIGN,FOLLOW_ASSIGN_in_statement1035); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_ASSIGN.add(string_literal71);

					char_literal72=(Token)match(input,TIMES,FOLLOW_TIMES_in_statement1037); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_TIMES.add(char_literal72);

					char_literal73=(Token)match(input,63,FOLLOW_63_in_statement1039); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_63.add(char_literal73);

					// AST REWRITE
					// elements: ID
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (DafnyTree)adaptor.nil();
					// 186:21: -> ^( HAVOC ID )
					{
						// Dafny.g:186:24: ^( HAVOC ID )
						{
						DafnyTree root_1 = (DafnyTree)adaptor.nil();
						root_1 = (DafnyTree)adaptor.becomeRoot((DafnyTree)adaptor.create(HAVOC, "HAVOC"), root_1);
						adaptor.addChild(root_1, stream_ID.nextNode());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;
				case 3 :
					// Dafny.g:187:5: ID ':=' ^ expression ';' !
					{
					root_0 = (DafnyTree)adaptor.nil();


					ID74=(Token)match(input,ID,FOLLOW_ID_in_statement1053); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					ID74_tree = (DafnyTree)adaptor.create(ID74);
					adaptor.addChild(root_0, ID74_tree);
					}

					string_literal75=(Token)match(input,ASSIGN,FOLLOW_ASSIGN_in_statement1055); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					string_literal75_tree = (DafnyTree)adaptor.create(string_literal75);
					root_0 = (DafnyTree)adaptor.becomeRoot(string_literal75_tree, root_0);
					}

					pushFollow(FOLLOW_expression_in_statement1058);
					expression76=expression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, expression76.getTree());

					char_literal77=(Token)match(input,63,FOLLOW_63_in_statement1060); if (state.failed) return retval;
					}
					break;
				case 4 :
					// Dafny.g:188:5: ID '[' i= expression ']' ass= ':=' v= expression ';'
					{
					ID78=(Token)match(input,ID,FOLLOW_ID_in_statement1067); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_ID.add(ID78);

					char_literal79=(Token)match(input,64,FOLLOW_64_in_statement1069); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_64.add(char_literal79);

					pushFollow(FOLLOW_expression_in_statement1073);
					i=expression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_expression.add(i.getTree());
					char_literal80=(Token)match(input,65,FOLLOW_65_in_statement1075); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_65.add(char_literal80);

					ass=(Token)match(input,ASSIGN,FOLLOW_ASSIGN_in_statement1079); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_ASSIGN.add(ass);

					pushFollow(FOLLOW_expression_in_statement1083);
					v=expression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_expression.add(v.getTree());
					char_literal81=(Token)match(input,63,FOLLOW_63_in_statement1085); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_63.add(char_literal81);

					// AST REWRITE
					// elements: i, ID, v
					// token labels: 
					// rule labels: v, retval, i
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_v=new RewriteRuleSubtreeStream(adaptor,"rule v",v!=null?v.getTree():null);
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);
					RewriteRuleSubtreeStream stream_i=new RewriteRuleSubtreeStream(adaptor,"rule i",i!=null?i.getTree():null);

					root_0 = (DafnyTree)adaptor.nil();
					// 189:9: -> ^( ARRAY_UPDATE[$ass] ID $i $v)
					{
						// Dafny.g:189:12: ^( ARRAY_UPDATE[$ass] ID $i $v)
						{
						DafnyTree root_1 = (DafnyTree)adaptor.nil();
						root_1 = (DafnyTree)adaptor.becomeRoot((DafnyTree)adaptor.create(ARRAY_UPDATE, ass), root_1);
						adaptor.addChild(root_1, stream_ID.nextNode());
						adaptor.addChild(root_1, stream_i.nextTree());
						adaptor.addChild(root_1, stream_v.nextTree());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;
				case 5 :
					// Dafny.g:190:5: ( ID ':=' 'call' )=>r= ID ':=' 'call' f= ID '(' ( expressions )? ')' ';'
					{
					r=(Token)match(input,ID,FOLLOW_ID_in_statement1126); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_ID.add(r);

					string_literal82=(Token)match(input,ASSIGN,FOLLOW_ASSIGN_in_statement1128); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_ASSIGN.add(string_literal82);

					string_literal83=(Token)match(input,CALL,FOLLOW_CALL_in_statement1130); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_CALL.add(string_literal83);

					f=(Token)match(input,ID,FOLLOW_ID_in_statement1134); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_ID.add(f);

					char_literal84=(Token)match(input,59,FOLLOW_59_in_statement1136); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_59.add(char_literal84);

					// Dafny.g:190:51: ( expressions )?
					int alt19=2;
					int LA19_0 = input.LA(1);
					if ( (LA19_0==BLOCK_BEGIN||LA19_0==ID||LA19_0==LIT||LA19_0==MINUS||LA19_0==NOT||LA19_0==59||LA19_0==64) ) {
						alt19=1;
					}
					switch (alt19) {
						case 1 :
							// Dafny.g:190:51: expressions
							{
							pushFollow(FOLLOW_expressions_in_statement1138);
							expressions85=expressions();
							state._fsp--;
							if (state.failed) return retval;
							if ( state.backtracking==0 ) stream_expressions.add(expressions85.getTree());
							}
							break;

					}

					char_literal86=(Token)match(input,60,FOLLOW_60_in_statement1141); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_60.add(char_literal86);

					char_literal87=(Token)match(input,63,FOLLOW_63_in_statement1143); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_63.add(char_literal87);

					// AST REWRITE
					// elements: CALL, r, expressions, f
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
					// 191:9: -> ^( 'call' $f ^( RESULTS $r) ^( ARGS ( expressions )? ) )
					{
						// Dafny.g:191:12: ^( 'call' $f ^( RESULTS $r) ^( ARGS ( expressions )? ) )
						{
						DafnyTree root_1 = (DafnyTree)adaptor.nil();
						root_1 = (DafnyTree)adaptor.becomeRoot(stream_CALL.nextNode(), root_1);
						adaptor.addChild(root_1, stream_f.nextNode());
						// Dafny.g:191:24: ^( RESULTS $r)
						{
						DafnyTree root_2 = (DafnyTree)adaptor.nil();
						root_2 = (DafnyTree)adaptor.becomeRoot((DafnyTree)adaptor.create(RESULTS, "RESULTS"), root_2);
						adaptor.addChild(root_2, stream_r.nextNode());
						adaptor.addChild(root_1, root_2);
						}

						// Dafny.g:191:38: ^( ARGS ( expressions )? )
						{
						DafnyTree root_2 = (DafnyTree)adaptor.nil();
						root_2 = (DafnyTree)adaptor.becomeRoot((DafnyTree)adaptor.create(ARGS, "ARGS"), root_2);
						// Dafny.g:191:45: ( expressions )?
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
				case 6 :
					// Dafny.g:192:5: ids ':=' 'call' ID '(' ( expressions )? ')' ';'
					{
					pushFollow(FOLLOW_ids_in_statement1180);
					ids88=ids();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_ids.add(ids88.getTree());
					string_literal89=(Token)match(input,ASSIGN,FOLLOW_ASSIGN_in_statement1182); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_ASSIGN.add(string_literal89);

					string_literal90=(Token)match(input,CALL,FOLLOW_CALL_in_statement1184); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_CALL.add(string_literal90);

					ID91=(Token)match(input,ID,FOLLOW_ID_in_statement1186); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_ID.add(ID91);

					char_literal92=(Token)match(input,59,FOLLOW_59_in_statement1188); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_59.add(char_literal92);

					// Dafny.g:192:28: ( expressions )?
					int alt20=2;
					int LA20_0 = input.LA(1);
					if ( (LA20_0==BLOCK_BEGIN||LA20_0==ID||LA20_0==LIT||LA20_0==MINUS||LA20_0==NOT||LA20_0==59||LA20_0==64) ) {
						alt20=1;
					}
					switch (alt20) {
						case 1 :
							// Dafny.g:192:28: expressions
							{
							pushFollow(FOLLOW_expressions_in_statement1190);
							expressions93=expressions();
							state._fsp--;
							if (state.failed) return retval;
							if ( state.backtracking==0 ) stream_expressions.add(expressions93.getTree());
							}
							break;

					}

					char_literal94=(Token)match(input,60,FOLLOW_60_in_statement1193); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_60.add(char_literal94);

					char_literal95=(Token)match(input,63,FOLLOW_63_in_statement1195); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_63.add(char_literal95);

					// AST REWRITE
					// elements: ID, CALL, expressions, ids
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (DafnyTree)adaptor.nil();
					// 193:9: -> ^( 'call' ID ^( RESULTS ids ) ^( ARGS ( expressions )? ) )
					{
						// Dafny.g:193:12: ^( 'call' ID ^( RESULTS ids ) ^( ARGS ( expressions )? ) )
						{
						DafnyTree root_1 = (DafnyTree)adaptor.nil();
						root_1 = (DafnyTree)adaptor.becomeRoot(stream_CALL.nextNode(), root_1);
						adaptor.addChild(root_1, stream_ID.nextNode());
						// Dafny.g:193:24: ^( RESULTS ids )
						{
						DafnyTree root_2 = (DafnyTree)adaptor.nil();
						root_2 = (DafnyTree)adaptor.becomeRoot((DafnyTree)adaptor.create(RESULTS, "RESULTS"), root_2);
						adaptor.addChild(root_2, stream_ids.nextTree());
						adaptor.addChild(root_1, root_2);
						}

						// Dafny.g:193:39: ^( ARGS ( expressions )? )
						{
						DafnyTree root_2 = (DafnyTree)adaptor.nil();
						root_2 = (DafnyTree)adaptor.becomeRoot((DafnyTree)adaptor.create(ARGS, "ARGS"), root_2);
						// Dafny.g:193:46: ( expressions )?
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
				case 7 :
					// Dafny.g:194:5: ( label )? 'while' expression ( invariant )+ decreases relaxedBlock
					{
					// Dafny.g:194:5: ( label )?
					int alt21=2;
					int LA21_0 = input.LA(1);
					if ( (LA21_0==LABEL) ) {
						alt21=1;
					}
					switch (alt21) {
						case 1 :
							// Dafny.g:194:5: label
							{
							pushFollow(FOLLOW_label_in_statement1230);
							label96=label();
							state._fsp--;
							if (state.failed) return retval;
							if ( state.backtracking==0 ) stream_label.add(label96.getTree());
							}
							break;

					}

					string_literal97=(Token)match(input,WHILE,FOLLOW_WHILE_in_statement1239); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_WHILE.add(string_literal97);

					pushFollow(FOLLOW_expression_in_statement1241);
					expression98=expression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_expression.add(expression98.getTree());
					// Dafny.g:195:26: ( invariant )+
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
							// Dafny.g:195:26: invariant
							{
							pushFollow(FOLLOW_invariant_in_statement1243);
							invariant99=invariant();
							state._fsp--;
							if (state.failed) return retval;
							if ( state.backtracking==0 ) stream_invariant.add(invariant99.getTree());
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

					pushFollow(FOLLOW_decreases_in_statement1246);
					decreases100=decreases();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_decreases.add(decreases100.getTree());
					pushFollow(FOLLOW_relaxedBlock_in_statement1248);
					relaxedBlock101=relaxedBlock();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_relaxedBlock.add(relaxedBlock101.getTree());
					// AST REWRITE
					// elements: WHILE, relaxedBlock, decreases, invariant, expression, label
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (DafnyTree)adaptor.nil();
					// 196:9: -> ^( 'while' ( label )? expression ( invariant )+ decreases relaxedBlock )
					{
						// Dafny.g:196:12: ^( 'while' ( label )? expression ( invariant )+ decreases relaxedBlock )
						{
						DafnyTree root_1 = (DafnyTree)adaptor.nil();
						root_1 = (DafnyTree)adaptor.becomeRoot(stream_WHILE.nextNode(), root_1);
						// Dafny.g:196:22: ( label )?
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
				case 8 :
					// Dafny.g:197:5: ( label )? 'if' ^ expression relaxedBlock ( options {greedy=true; } : 'else' ! relaxedBlock )?
					{
					root_0 = (DafnyTree)adaptor.nil();


					// Dafny.g:197:5: ( label )?
					int alt23=2;
					int LA23_0 = input.LA(1);
					if ( (LA23_0==LABEL) ) {
						alt23=1;
					}
					switch (alt23) {
						case 1 :
							// Dafny.g:197:5: label
							{
							pushFollow(FOLLOW_label_in_statement1280);
							label102=label();
							state._fsp--;
							if (state.failed) return retval;
							if ( state.backtracking==0 ) adaptor.addChild(root_0, label102.getTree());

							}
							break;

					}

					string_literal103=(Token)match(input,IF,FOLLOW_IF_in_statement1283); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					string_literal103_tree = (DafnyTree)adaptor.create(string_literal103);
					root_0 = (DafnyTree)adaptor.becomeRoot(string_literal103_tree, root_0);
					}

					pushFollow(FOLLOW_expression_in_statement1286);
					expression104=expression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, expression104.getTree());

					pushFollow(FOLLOW_relaxedBlock_in_statement1288);
					relaxedBlock105=relaxedBlock();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, relaxedBlock105.getTree());

					// Dafny.g:198:7: ( options {greedy=true; } : 'else' ! relaxedBlock )?
					int alt24=2;
					int LA24_0 = input.LA(1);
					if ( (LA24_0==ELSE) ) {
						alt24=1;
					}
					switch (alt24) {
						case 1 :
							// Dafny.g:198:36: 'else' ! relaxedBlock
							{
							string_literal106=(Token)match(input,ELSE,FOLLOW_ELSE_in_statement1309); if (state.failed) return retval;
							pushFollow(FOLLOW_relaxedBlock_in_statement1312);
							relaxedBlock107=relaxedBlock();
							state._fsp--;
							if (state.failed) return retval;
							if ( state.backtracking==0 ) adaptor.addChild(root_0, relaxedBlock107.getTree());

							}
							break;

					}

					}
					break;
				case 9 :
					// Dafny.g:199:5: 'assert' ^ ( 'label' ! ID ':' !)? expression ';' !
					{
					root_0 = (DafnyTree)adaptor.nil();


					string_literal108=(Token)match(input,ASSERT,FOLLOW_ASSERT_in_statement1321); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					string_literal108_tree = (DafnyTree)adaptor.create(string_literal108);
					root_0 = (DafnyTree)adaptor.becomeRoot(string_literal108_tree, root_0);
					}

					// Dafny.g:199:15: ( 'label' ! ID ':' !)?
					int alt25=2;
					int LA25_0 = input.LA(1);
					if ( (LA25_0==LABEL) ) {
						alt25=1;
					}
					switch (alt25) {
						case 1 :
							// Dafny.g:199:17: 'label' ! ID ':' !
							{
							string_literal109=(Token)match(input,LABEL,FOLLOW_LABEL_in_statement1326); if (state.failed) return retval;
							ID110=(Token)match(input,ID,FOLLOW_ID_in_statement1329); if (state.failed) return retval;
							if ( state.backtracking==0 ) {
							ID110_tree = (DafnyTree)adaptor.create(ID110);
							adaptor.addChild(root_0, ID110_tree);
							}

							char_literal111=(Token)match(input,62,FOLLOW_62_in_statement1331); if (state.failed) return retval;
							}
							break;

					}

					pushFollow(FOLLOW_expression_in_statement1337);
					expression112=expression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, expression112.getTree());

					char_literal113=(Token)match(input,63,FOLLOW_63_in_statement1339); if (state.failed) return retval;
					}
					break;
				case 10 :
					// Dafny.g:200:5: 'assume' ^ ( 'label' ! ID ':' !)? expression ';' !
					{
					root_0 = (DafnyTree)adaptor.nil();


					string_literal114=(Token)match(input,ASSUME,FOLLOW_ASSUME_in_statement1346); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					string_literal114_tree = (DafnyTree)adaptor.create(string_literal114);
					root_0 = (DafnyTree)adaptor.becomeRoot(string_literal114_tree, root_0);
					}

					// Dafny.g:200:15: ( 'label' ! ID ':' !)?
					int alt26=2;
					int LA26_0 = input.LA(1);
					if ( (LA26_0==LABEL) ) {
						alt26=1;
					}
					switch (alt26) {
						case 1 :
							// Dafny.g:200:17: 'label' ! ID ':' !
							{
							string_literal115=(Token)match(input,LABEL,FOLLOW_LABEL_in_statement1351); if (state.failed) return retval;
							ID116=(Token)match(input,ID,FOLLOW_ID_in_statement1354); if (state.failed) return retval;
							if ( state.backtracking==0 ) {
							ID116_tree = (DafnyTree)adaptor.create(ID116);
							adaptor.addChild(root_0, ID116_tree);
							}

							char_literal117=(Token)match(input,62,FOLLOW_62_in_statement1356); if (state.failed) return retval;
							}
							break;

					}

					pushFollow(FOLLOW_expression_in_statement1362);
					expression118=expression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, expression118.getTree());

					char_literal119=(Token)match(input,63,FOLLOW_63_in_statement1364); if (state.failed) return retval;
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
	// Dafny.g:203:1: ids : ID ( ',' ! ID )+ ;
	public final DafnyParser.ids_return ids() throws RecognitionException {
		DafnyParser.ids_return retval = new DafnyParser.ids_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		Token ID120=null;
		Token char_literal121=null;
		Token ID122=null;

		DafnyTree ID120_tree=null;
		DafnyTree char_literal121_tree=null;
		DafnyTree ID122_tree=null;

		try {
			// Dafny.g:203:4: ( ID ( ',' ! ID )+ )
			// Dafny.g:204:3: ID ( ',' ! ID )+
			{
			root_0 = (DafnyTree)adaptor.nil();


			ID120=(Token)match(input,ID,FOLLOW_ID_in_ids1377); if (state.failed) return retval;
			if ( state.backtracking==0 ) {
			ID120_tree = (DafnyTree)adaptor.create(ID120);
			adaptor.addChild(root_0, ID120_tree);
			}

			// Dafny.g:204:6: ( ',' ! ID )+
			int cnt28=0;
			loop28:
			while (true) {
				int alt28=2;
				int LA28_0 = input.LA(1);
				if ( (LA28_0==61) ) {
					alt28=1;
				}

				switch (alt28) {
				case 1 :
					// Dafny.g:204:7: ',' ! ID
					{
					char_literal121=(Token)match(input,61,FOLLOW_61_in_ids1380); if (state.failed) return retval;
					ID122=(Token)match(input,ID,FOLLOW_ID_in_ids1383); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					ID122_tree = (DafnyTree)adaptor.create(ID122);
					adaptor.addChild(root_0, ID122_tree);
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
	// Dafny.g:207:1: expressions : expression ( ',' ! expression )* ;
	public final DafnyParser.expressions_return expressions() throws RecognitionException {
		DafnyParser.expressions_return retval = new DafnyParser.expressions_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		Token char_literal124=null;
		ParserRuleReturnScope expression123 =null;
		ParserRuleReturnScope expression125 =null;

		DafnyTree char_literal124_tree=null;

		try {
			// Dafny.g:207:12: ( expression ( ',' ! expression )* )
			// Dafny.g:208:3: expression ( ',' ! expression )*
			{
			root_0 = (DafnyTree)adaptor.nil();


			pushFollow(FOLLOW_expression_in_expressions1397);
			expression123=expression();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, expression123.getTree());

			// Dafny.g:208:14: ( ',' ! expression )*
			loop29:
			while (true) {
				int alt29=2;
				int LA29_0 = input.LA(1);
				if ( (LA29_0==61) ) {
					alt29=1;
				}

				switch (alt29) {
				case 1 :
					// Dafny.g:208:16: ',' ! expression
					{
					char_literal124=(Token)match(input,61,FOLLOW_61_in_expressions1401); if (state.failed) return retval;
					pushFollow(FOLLOW_expression_in_expressions1404);
					expression125=expression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, expression125.getTree());

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
	// Dafny.g:211:1: expression : or_expr ;
	public final DafnyParser.expression_return expression() throws RecognitionException {
		DafnyParser.expression_return retval = new DafnyParser.expression_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		ParserRuleReturnScope or_expr126 =null;


		try {
			// Dafny.g:211:11: ( or_expr )
			// Dafny.g:212:3: or_expr
			{
			root_0 = (DafnyTree)adaptor.nil();


			pushFollow(FOLLOW_or_expr_in_expression1419);
			or_expr126=or_expr();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, or_expr126.getTree());

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
	// Dafny.g:214:1: or_expr : and_expr ( ( '||' ^| '==>' ^) or_expr )? ;
	public final DafnyParser.or_expr_return or_expr() throws RecognitionException {
		DafnyParser.or_expr_return retval = new DafnyParser.or_expr_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		Token string_literal128=null;
		Token string_literal129=null;
		ParserRuleReturnScope and_expr127 =null;
		ParserRuleReturnScope or_expr130 =null;

		DafnyTree string_literal128_tree=null;
		DafnyTree string_literal129_tree=null;

		try {
			// Dafny.g:214:8: ( and_expr ( ( '||' ^| '==>' ^) or_expr )? )
			// Dafny.g:215:3: and_expr ( ( '||' ^| '==>' ^) or_expr )?
			{
			root_0 = (DafnyTree)adaptor.nil();


			pushFollow(FOLLOW_and_expr_in_or_expr1428);
			and_expr127=and_expr();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, and_expr127.getTree());

			// Dafny.g:215:12: ( ( '||' ^| '==>' ^) or_expr )?
			int alt31=2;
			int LA31_0 = input.LA(1);
			if ( (LA31_0==IMPLIES||LA31_0==OR) ) {
				alt31=1;
			}
			switch (alt31) {
				case 1 :
					// Dafny.g:215:14: ( '||' ^| '==>' ^) or_expr
					{
					// Dafny.g:215:14: ( '||' ^| '==>' ^)
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
							// Dafny.g:215:15: '||' ^
							{
							string_literal128=(Token)match(input,OR,FOLLOW_OR_in_or_expr1433); if (state.failed) return retval;
							if ( state.backtracking==0 ) {
							string_literal128_tree = (DafnyTree)adaptor.create(string_literal128);
							root_0 = (DafnyTree)adaptor.becomeRoot(string_literal128_tree, root_0);
							}

							}
							break;
						case 2 :
							// Dafny.g:215:23: '==>' ^
							{
							string_literal129=(Token)match(input,IMPLIES,FOLLOW_IMPLIES_in_or_expr1438); if (state.failed) return retval;
							if ( state.backtracking==0 ) {
							string_literal129_tree = (DafnyTree)adaptor.create(string_literal129);
							root_0 = (DafnyTree)adaptor.becomeRoot(string_literal129_tree, root_0);
							}

							}
							break;

					}

					pushFollow(FOLLOW_or_expr_in_or_expr1442);
					or_expr130=or_expr();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, or_expr130.getTree());

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
	// Dafny.g:218:1: and_expr : rel_expr ( '&&' ^ and_expr )? ;
	public final DafnyParser.and_expr_return and_expr() throws RecognitionException {
		DafnyParser.and_expr_return retval = new DafnyParser.and_expr_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		Token string_literal132=null;
		ParserRuleReturnScope rel_expr131 =null;
		ParserRuleReturnScope and_expr133 =null;

		DafnyTree string_literal132_tree=null;

		try {
			// Dafny.g:218:9: ( rel_expr ( '&&' ^ and_expr )? )
			// Dafny.g:219:3: rel_expr ( '&&' ^ and_expr )?
			{
			root_0 = (DafnyTree)adaptor.nil();


			pushFollow(FOLLOW_rel_expr_in_and_expr1457);
			rel_expr131=rel_expr();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, rel_expr131.getTree());

			// Dafny.g:219:12: ( '&&' ^ and_expr )?
			int alt32=2;
			int LA32_0 = input.LA(1);
			if ( (LA32_0==AND) ) {
				alt32=1;
			}
			switch (alt32) {
				case 1 :
					// Dafny.g:219:14: '&&' ^ and_expr
					{
					string_literal132=(Token)match(input,AND,FOLLOW_AND_in_and_expr1461); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					string_literal132_tree = (DafnyTree)adaptor.create(string_literal132);
					root_0 = (DafnyTree)adaptor.becomeRoot(string_literal132_tree, root_0);
					}

					pushFollow(FOLLOW_and_expr_in_and_expr1464);
					and_expr133=and_expr();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, and_expr133.getTree());

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
	// Dafny.g:222:1: rel_expr : add_expr ( ( '<' ^| '>' ^| '==' ^| '<=' ^| '>=' ^) add_expr )? ;
	public final DafnyParser.rel_expr_return rel_expr() throws RecognitionException {
		DafnyParser.rel_expr_return retval = new DafnyParser.rel_expr_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		Token char_literal135=null;
		Token char_literal136=null;
		Token string_literal137=null;
		Token string_literal138=null;
		Token string_literal139=null;
		ParserRuleReturnScope add_expr134 =null;
		ParserRuleReturnScope add_expr140 =null;

		DafnyTree char_literal135_tree=null;
		DafnyTree char_literal136_tree=null;
		DafnyTree string_literal137_tree=null;
		DafnyTree string_literal138_tree=null;
		DafnyTree string_literal139_tree=null;

		try {
			// Dafny.g:222:9: ( add_expr ( ( '<' ^| '>' ^| '==' ^| '<=' ^| '>=' ^) add_expr )? )
			// Dafny.g:223:3: add_expr ( ( '<' ^| '>' ^| '==' ^| '<=' ^| '>=' ^) add_expr )?
			{
			root_0 = (DafnyTree)adaptor.nil();


			pushFollow(FOLLOW_add_expr_in_rel_expr1479);
			add_expr134=add_expr();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, add_expr134.getTree());

			// Dafny.g:223:12: ( ( '<' ^| '>' ^| '==' ^| '<=' ^| '>=' ^) add_expr )?
			int alt34=2;
			int LA34_0 = input.LA(1);
			if ( (LA34_0==EQ||(LA34_0 >= GE && LA34_0 <= GT)||LA34_0==LE||LA34_0==LT) ) {
				alt34=1;
			}
			switch (alt34) {
				case 1 :
					// Dafny.g:223:14: ( '<' ^| '>' ^| '==' ^| '<=' ^| '>=' ^) add_expr
					{
					// Dafny.g:223:14: ( '<' ^| '>' ^| '==' ^| '<=' ^| '>=' ^)
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
							// Dafny.g:223:15: '<' ^
							{
							char_literal135=(Token)match(input,LT,FOLLOW_LT_in_rel_expr1484); if (state.failed) return retval;
							if ( state.backtracking==0 ) {
							char_literal135_tree = (DafnyTree)adaptor.create(char_literal135);
							root_0 = (DafnyTree)adaptor.becomeRoot(char_literal135_tree, root_0);
							}

							}
							break;
						case 2 :
							// Dafny.g:223:22: '>' ^
							{
							char_literal136=(Token)match(input,GT,FOLLOW_GT_in_rel_expr1489); if (state.failed) return retval;
							if ( state.backtracking==0 ) {
							char_literal136_tree = (DafnyTree)adaptor.create(char_literal136);
							root_0 = (DafnyTree)adaptor.becomeRoot(char_literal136_tree, root_0);
							}

							}
							break;
						case 3 :
							// Dafny.g:223:29: '==' ^
							{
							string_literal137=(Token)match(input,EQ,FOLLOW_EQ_in_rel_expr1494); if (state.failed) return retval;
							if ( state.backtracking==0 ) {
							string_literal137_tree = (DafnyTree)adaptor.create(string_literal137);
							root_0 = (DafnyTree)adaptor.becomeRoot(string_literal137_tree, root_0);
							}

							}
							break;
						case 4 :
							// Dafny.g:223:37: '<=' ^
							{
							string_literal138=(Token)match(input,LE,FOLLOW_LE_in_rel_expr1499); if (state.failed) return retval;
							if ( state.backtracking==0 ) {
							string_literal138_tree = (DafnyTree)adaptor.create(string_literal138);
							root_0 = (DafnyTree)adaptor.becomeRoot(string_literal138_tree, root_0);
							}

							}
							break;
						case 5 :
							// Dafny.g:223:45: '>=' ^
							{
							string_literal139=(Token)match(input,GE,FOLLOW_GE_in_rel_expr1504); if (state.failed) return retval;
							if ( state.backtracking==0 ) {
							string_literal139_tree = (DafnyTree)adaptor.create(string_literal139);
							root_0 = (DafnyTree)adaptor.becomeRoot(string_literal139_tree, root_0);
							}

							}
							break;

					}

					pushFollow(FOLLOW_add_expr_in_rel_expr1508);
					add_expr140=add_expr();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, add_expr140.getTree());

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
	// Dafny.g:226:1: add_expr : mul_expr ( ( '+' | '-' | '++' ) ^ add_expr )? ;
	public final DafnyParser.add_expr_return add_expr() throws RecognitionException {
		DafnyParser.add_expr_return retval = new DafnyParser.add_expr_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		Token set142=null;
		ParserRuleReturnScope mul_expr141 =null;
		ParserRuleReturnScope add_expr143 =null;

		DafnyTree set142_tree=null;

		try {
			// Dafny.g:226:9: ( mul_expr ( ( '+' | '-' | '++' ) ^ add_expr )? )
			// Dafny.g:227:3: mul_expr ( ( '+' | '-' | '++' ) ^ add_expr )?
			{
			root_0 = (DafnyTree)adaptor.nil();


			pushFollow(FOLLOW_mul_expr_in_add_expr1523);
			mul_expr141=mul_expr();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, mul_expr141.getTree());

			// Dafny.g:227:12: ( ( '+' | '-' | '++' ) ^ add_expr )?
			int alt35=2;
			int LA35_0 = input.LA(1);
			if ( (LA35_0==MINUS||LA35_0==PLUS||LA35_0==UNION) ) {
				alt35=1;
			}
			switch (alt35) {
				case 1 :
					// Dafny.g:227:14: ( '+' | '-' | '++' ) ^ add_expr
					{
					set142=input.LT(1);
					set142=input.LT(1);
					if ( input.LA(1)==MINUS||input.LA(1)==PLUS||input.LA(1)==UNION ) {
						input.consume();
						if ( state.backtracking==0 ) root_0 = (DafnyTree)adaptor.becomeRoot((DafnyTree)adaptor.create(set142), root_0);
						state.errorRecovery=false;
						state.failed=false;
					}
					else {
						if (state.backtracking>0) {state.failed=true; return retval;}
						MismatchedSetException mse = new MismatchedSetException(null,input);
						throw mse;
					}
					pushFollow(FOLLOW_add_expr_in_add_expr1540);
					add_expr143=add_expr();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, add_expr143.getTree());

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
	// Dafny.g:230:1: mul_expr : prefix_expr ( ( '*' | '**' ) ^ mul_expr )? ;
	public final DafnyParser.mul_expr_return mul_expr() throws RecognitionException {
		DafnyParser.mul_expr_return retval = new DafnyParser.mul_expr_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		Token set145=null;
		ParserRuleReturnScope prefix_expr144 =null;
		ParserRuleReturnScope mul_expr146 =null;

		DafnyTree set145_tree=null;

		try {
			// Dafny.g:230:9: ( prefix_expr ( ( '*' | '**' ) ^ mul_expr )? )
			// Dafny.g:231:3: prefix_expr ( ( '*' | '**' ) ^ mul_expr )?
			{
			root_0 = (DafnyTree)adaptor.nil();


			pushFollow(FOLLOW_prefix_expr_in_mul_expr1555);
			prefix_expr144=prefix_expr();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, prefix_expr144.getTree());

			// Dafny.g:231:15: ( ( '*' | '**' ) ^ mul_expr )?
			int alt36=2;
			int LA36_0 = input.LA(1);
			if ( (LA36_0==INTERSECT||LA36_0==TIMES) ) {
				alt36=1;
			}
			switch (alt36) {
				case 1 :
					// Dafny.g:231:17: ( '*' | '**' ) ^ mul_expr
					{
					set145=input.LT(1);
					set145=input.LT(1);
					if ( input.LA(1)==INTERSECT||input.LA(1)==TIMES ) {
						input.consume();
						if ( state.backtracking==0 ) root_0 = (DafnyTree)adaptor.becomeRoot((DafnyTree)adaptor.create(set145), root_0);
						state.errorRecovery=false;
						state.failed=false;
					}
					else {
						if (state.backtracking>0) {state.failed=true; return retval;}
						MismatchedSetException mse = new MismatchedSetException(null,input);
						throw mse;
					}
					pushFollow(FOLLOW_mul_expr_in_mul_expr1568);
					mul_expr146=mul_expr();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, mul_expr146.getTree());

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
	// Dafny.g:234:1: prefix_expr : ( '-' ^ prefix_expr | '!' ^ prefix_expr | postfix_expr );
	public final DafnyParser.prefix_expr_return prefix_expr() throws RecognitionException {
		DafnyParser.prefix_expr_return retval = new DafnyParser.prefix_expr_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		Token char_literal147=null;
		Token char_literal149=null;
		ParserRuleReturnScope prefix_expr148 =null;
		ParserRuleReturnScope prefix_expr150 =null;
		ParserRuleReturnScope postfix_expr151 =null;

		DafnyTree char_literal147_tree=null;
		DafnyTree char_literal149_tree=null;

		try {
			// Dafny.g:234:12: ( '-' ^ prefix_expr | '!' ^ prefix_expr | postfix_expr )
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
			case 59:
			case 64:
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
					// Dafny.g:235:5: '-' ^ prefix_expr
					{
					root_0 = (DafnyTree)adaptor.nil();


					char_literal147=(Token)match(input,MINUS,FOLLOW_MINUS_in_prefix_expr1585); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					char_literal147_tree = (DafnyTree)adaptor.create(char_literal147);
					root_0 = (DafnyTree)adaptor.becomeRoot(char_literal147_tree, root_0);
					}

					pushFollow(FOLLOW_prefix_expr_in_prefix_expr1588);
					prefix_expr148=prefix_expr();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, prefix_expr148.getTree());

					}
					break;
				case 2 :
					// Dafny.g:236:5: '!' ^ prefix_expr
					{
					root_0 = (DafnyTree)adaptor.nil();


					char_literal149=(Token)match(input,NOT,FOLLOW_NOT_in_prefix_expr1594); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					char_literal149_tree = (DafnyTree)adaptor.create(char_literal149);
					root_0 = (DafnyTree)adaptor.becomeRoot(char_literal149_tree, root_0);
					}

					pushFollow(FOLLOW_prefix_expr_in_prefix_expr1597);
					prefix_expr150=prefix_expr();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, prefix_expr150.getTree());

					}
					break;
				case 3 :
					// Dafny.g:237:5: postfix_expr
					{
					root_0 = (DafnyTree)adaptor.nil();


					pushFollow(FOLLOW_postfix_expr_in_prefix_expr1603);
					postfix_expr151=postfix_expr();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, postfix_expr151.getTree());

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
	// Dafny.g:240:1: postfix_expr : atom_expr ( '[' expression ']' -> ^( ARRAY_ACCESS atom_expr expression ) | '.' LENGTH -> ^( LENGTH atom_expr ) | -> atom_expr | EOF -> atom_expr ) ;
	public final DafnyParser.postfix_expr_return postfix_expr() throws RecognitionException {
		DafnyParser.postfix_expr_return retval = new DafnyParser.postfix_expr_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		Token char_literal153=null;
		Token char_literal155=null;
		Token char_literal156=null;
		Token LENGTH157=null;
		Token EOF158=null;
		ParserRuleReturnScope atom_expr152 =null;
		ParserRuleReturnScope expression154 =null;

		DafnyTree char_literal153_tree=null;
		DafnyTree char_literal155_tree=null;
		DafnyTree char_literal156_tree=null;
		DafnyTree LENGTH157_tree=null;
		DafnyTree EOF158_tree=null;
		RewriteRuleTokenStream stream_DOT=new RewriteRuleTokenStream(adaptor,"token DOT");
		RewriteRuleTokenStream stream_64=new RewriteRuleTokenStream(adaptor,"token 64");
		RewriteRuleTokenStream stream_65=new RewriteRuleTokenStream(adaptor,"token 65");
		RewriteRuleTokenStream stream_EOF=new RewriteRuleTokenStream(adaptor,"token EOF");
		RewriteRuleTokenStream stream_LENGTH=new RewriteRuleTokenStream(adaptor,"token LENGTH");
		RewriteRuleSubtreeStream stream_expression=new RewriteRuleSubtreeStream(adaptor,"rule expression");
		RewriteRuleSubtreeStream stream_atom_expr=new RewriteRuleSubtreeStream(adaptor,"rule atom_expr");

		try {
			// Dafny.g:240:13: ( atom_expr ( '[' expression ']' -> ^( ARRAY_ACCESS atom_expr expression ) | '.' LENGTH -> ^( LENGTH atom_expr ) | -> atom_expr | EOF -> atom_expr ) )
			// Dafny.g:241:3: atom_expr ( '[' expression ']' -> ^( ARRAY_ACCESS atom_expr expression ) | '.' LENGTH -> ^( LENGTH atom_expr ) | -> atom_expr | EOF -> atom_expr )
			{
			pushFollow(FOLLOW_atom_expr_in_postfix_expr1615);
			atom_expr152=atom_expr();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) stream_atom_expr.add(atom_expr152.getTree());
			// Dafny.g:242:3: ( '[' expression ']' -> ^( ARRAY_ACCESS atom_expr expression ) | '.' LENGTH -> ^( LENGTH atom_expr ) | -> atom_expr | EOF -> atom_expr )
			int alt38=4;
			switch ( input.LA(1) ) {
			case 64:
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
			case 60:
			case 61:
			case 63:
			case 65:
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
					// Dafny.g:242:5: '[' expression ']'
					{
					char_literal153=(Token)match(input,64,FOLLOW_64_in_postfix_expr1621); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_64.add(char_literal153);

					pushFollow(FOLLOW_expression_in_postfix_expr1623);
					expression154=expression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_expression.add(expression154.getTree());
					char_literal155=(Token)match(input,65,FOLLOW_65_in_postfix_expr1625); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_65.add(char_literal155);

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
					// 242:24: -> ^( ARRAY_ACCESS atom_expr expression )
					{
						// Dafny.g:242:27: ^( ARRAY_ACCESS atom_expr expression )
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
					// Dafny.g:243:5: '.' LENGTH
					{
					char_literal156=(Token)match(input,DOT,FOLLOW_DOT_in_postfix_expr1643); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_DOT.add(char_literal156);

					LENGTH157=(Token)match(input,LENGTH,FOLLOW_LENGTH_in_postfix_expr1645); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_LENGTH.add(LENGTH157);

					// AST REWRITE
					// elements: LENGTH, atom_expr
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (DafnyTree)adaptor.nil();
					// 243:16: -> ^( LENGTH atom_expr )
					{
						// Dafny.g:243:19: ^( LENGTH atom_expr )
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
					// Dafny.g:244:5: 
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
					// 244:5: -> atom_expr
					{
						adaptor.addChild(root_0, stream_atom_expr.nextTree());
					}


					retval.tree = root_0;
					}

					}
					break;
				case 4 :
					// Dafny.g:245:5: EOF
					{
					EOF158=(Token)match(input,EOF,FOLLOW_EOF_in_postfix_expr1669); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_EOF.add(EOF158);

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
					// 245:9: -> atom_expr
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
	// Dafny.g:249:1: atom_expr : ( ID | LIT | quantifier | '(' ! expression ')' !| '{' ( expressions )? '}' -> ^( SETEX ( expressions )? ) | '[' ( expressions )? ']' -> ^( LISTEX ( expressions )? ) );
	public final DafnyParser.atom_expr_return atom_expr() throws RecognitionException {
		DafnyParser.atom_expr_return retval = new DafnyParser.atom_expr_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		Token ID159=null;
		Token LIT160=null;
		Token char_literal162=null;
		Token char_literal164=null;
		Token char_literal165=null;
		Token char_literal167=null;
		Token char_literal168=null;
		Token char_literal170=null;
		ParserRuleReturnScope quantifier161 =null;
		ParserRuleReturnScope expression163 =null;
		ParserRuleReturnScope expressions166 =null;
		ParserRuleReturnScope expressions169 =null;

		DafnyTree ID159_tree=null;
		DafnyTree LIT160_tree=null;
		DafnyTree char_literal162_tree=null;
		DafnyTree char_literal164_tree=null;
		DafnyTree char_literal165_tree=null;
		DafnyTree char_literal167_tree=null;
		DafnyTree char_literal168_tree=null;
		DafnyTree char_literal170_tree=null;
		RewriteRuleTokenStream stream_64=new RewriteRuleTokenStream(adaptor,"token 64");
		RewriteRuleTokenStream stream_65=new RewriteRuleTokenStream(adaptor,"token 65");
		RewriteRuleTokenStream stream_BLOCK_BEGIN=new RewriteRuleTokenStream(adaptor,"token BLOCK_BEGIN");
		RewriteRuleTokenStream stream_BLOCK_END=new RewriteRuleTokenStream(adaptor,"token BLOCK_END");
		RewriteRuleSubtreeStream stream_expressions=new RewriteRuleSubtreeStream(adaptor,"rule expressions");

		try {
			// Dafny.g:249:10: ( ID | LIT | quantifier | '(' ! expression ')' !| '{' ( expressions )? '}' -> ^( SETEX ( expressions )? ) | '[' ( expressions )? ']' -> ^( LISTEX ( expressions )? ) )
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
			case 59:
				{
				int LA41_3 = input.LA(2);
				if ( (LA41_3==ALL||LA41_3==EX) ) {
					alt41=3;
				}
				else if ( (LA41_3==BLOCK_BEGIN||LA41_3==ID||LA41_3==LIT||LA41_3==MINUS||LA41_3==NOT||LA41_3==59||LA41_3==64) ) {
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
			case 64:
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
					// Dafny.g:250:5: ID
					{
					root_0 = (DafnyTree)adaptor.nil();


					ID159=(Token)match(input,ID,FOLLOW_ID_in_atom_expr1691); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					ID159_tree = (DafnyTree)adaptor.create(ID159);
					adaptor.addChild(root_0, ID159_tree);
					}

					}
					break;
				case 2 :
					// Dafny.g:251:5: LIT
					{
					root_0 = (DafnyTree)adaptor.nil();


					LIT160=(Token)match(input,LIT,FOLLOW_LIT_in_atom_expr1697); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					LIT160_tree = (DafnyTree)adaptor.create(LIT160);
					adaptor.addChild(root_0, LIT160_tree);
					}

					}
					break;
				case 3 :
					// Dafny.g:252:5: quantifier
					{
					root_0 = (DafnyTree)adaptor.nil();


					pushFollow(FOLLOW_quantifier_in_atom_expr1703);
					quantifier161=quantifier();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, quantifier161.getTree());

					}
					break;
				case 4 :
					// Dafny.g:253:5: '(' ! expression ')' !
					{
					root_0 = (DafnyTree)adaptor.nil();


					char_literal162=(Token)match(input,59,FOLLOW_59_in_atom_expr1709); if (state.failed) return retval;
					pushFollow(FOLLOW_expression_in_atom_expr1712);
					expression163=expression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, expression163.getTree());

					char_literal164=(Token)match(input,60,FOLLOW_60_in_atom_expr1714); if (state.failed) return retval;
					}
					break;
				case 5 :
					// Dafny.g:254:5: '{' ( expressions )? '}'
					{
					char_literal165=(Token)match(input,BLOCK_BEGIN,FOLLOW_BLOCK_BEGIN_in_atom_expr1721); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_BLOCK_BEGIN.add(char_literal165);

					// Dafny.g:254:9: ( expressions )?
					int alt39=2;
					int LA39_0 = input.LA(1);
					if ( (LA39_0==BLOCK_BEGIN||LA39_0==ID||LA39_0==LIT||LA39_0==MINUS||LA39_0==NOT||LA39_0==59||LA39_0==64) ) {
						alt39=1;
					}
					switch (alt39) {
						case 1 :
							// Dafny.g:254:9: expressions
							{
							pushFollow(FOLLOW_expressions_in_atom_expr1723);
							expressions166=expressions();
							state._fsp--;
							if (state.failed) return retval;
							if ( state.backtracking==0 ) stream_expressions.add(expressions166.getTree());
							}
							break;

					}

					char_literal167=(Token)match(input,BLOCK_END,FOLLOW_BLOCK_END_in_atom_expr1726); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_BLOCK_END.add(char_literal167);

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
					// 254:26: -> ^( SETEX ( expressions )? )
					{
						// Dafny.g:254:29: ^( SETEX ( expressions )? )
						{
						DafnyTree root_1 = (DafnyTree)adaptor.nil();
						root_1 = (DafnyTree)adaptor.becomeRoot((DafnyTree)adaptor.create(SETEX, "SETEX"), root_1);
						// Dafny.g:254:37: ( expressions )?
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
					// Dafny.g:255:5: '[' ( expressions )? ']'
					{
					char_literal168=(Token)match(input,64,FOLLOW_64_in_atom_expr1741); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_64.add(char_literal168);

					// Dafny.g:255:9: ( expressions )?
					int alt40=2;
					int LA40_0 = input.LA(1);
					if ( (LA40_0==BLOCK_BEGIN||LA40_0==ID||LA40_0==LIT||LA40_0==MINUS||LA40_0==NOT||LA40_0==59||LA40_0==64) ) {
						alt40=1;
					}
					switch (alt40) {
						case 1 :
							// Dafny.g:255:9: expressions
							{
							pushFollow(FOLLOW_expressions_in_atom_expr1743);
							expressions169=expressions();
							state._fsp--;
							if (state.failed) return retval;
							if ( state.backtracking==0 ) stream_expressions.add(expressions169.getTree());
							}
							break;

					}

					char_literal170=(Token)match(input,65,FOLLOW_65_in_atom_expr1746); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_65.add(char_literal170);

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
					// 255:26: -> ^( LISTEX ( expressions )? )
					{
						// Dafny.g:255:29: ^( LISTEX ( expressions )? )
						{
						DafnyTree root_1 = (DafnyTree)adaptor.nil();
						root_1 = (DafnyTree)adaptor.becomeRoot((DafnyTree)adaptor.create(LISTEX, "LISTEX"), root_1);
						// Dafny.g:255:38: ( expressions )?
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
	// Dafny.g:258:1: quantifier : '(' ! ( ALL ^| EX ^) ID ':' ! type '::' ! expression ')' !;
	public final DafnyParser.quantifier_return quantifier() throws RecognitionException {
		DafnyParser.quantifier_return retval = new DafnyParser.quantifier_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		Token char_literal171=null;
		Token ALL172=null;
		Token EX173=null;
		Token ID174=null;
		Token char_literal175=null;
		Token string_literal177=null;
		Token char_literal179=null;
		ParserRuleReturnScope type176 =null;
		ParserRuleReturnScope expression178 =null;

		DafnyTree char_literal171_tree=null;
		DafnyTree ALL172_tree=null;
		DafnyTree EX173_tree=null;
		DafnyTree ID174_tree=null;
		DafnyTree char_literal175_tree=null;
		DafnyTree string_literal177_tree=null;
		DafnyTree char_literal179_tree=null;

		try {
			// Dafny.g:258:11: ( '(' ! ( ALL ^| EX ^) ID ':' ! type '::' ! expression ')' !)
			// Dafny.g:259:3: '(' ! ( ALL ^| EX ^) ID ':' ! type '::' ! expression ')' !
			{
			root_0 = (DafnyTree)adaptor.nil();


			char_literal171=(Token)match(input,59,FOLLOW_59_in_quantifier1767); if (state.failed) return retval;
			// Dafny.g:259:8: ( ALL ^| EX ^)
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
					// Dafny.g:259:9: ALL ^
					{
					ALL172=(Token)match(input,ALL,FOLLOW_ALL_in_quantifier1771); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					ALL172_tree = (DafnyTree)adaptor.create(ALL172);
					root_0 = (DafnyTree)adaptor.becomeRoot(ALL172_tree, root_0);
					}

					}
					break;
				case 2 :
					// Dafny.g:259:16: EX ^
					{
					EX173=(Token)match(input,EX,FOLLOW_EX_in_quantifier1776); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					EX173_tree = (DafnyTree)adaptor.create(EX173);
					root_0 = (DafnyTree)adaptor.becomeRoot(EX173_tree, root_0);
					}

					}
					break;

			}

			ID174=(Token)match(input,ID,FOLLOW_ID_in_quantifier1780); if (state.failed) return retval;
			if ( state.backtracking==0 ) {
			ID174_tree = (DafnyTree)adaptor.create(ID174);
			adaptor.addChild(root_0, ID174_tree);
			}

			char_literal175=(Token)match(input,62,FOLLOW_62_in_quantifier1782); if (state.failed) return retval;
			pushFollow(FOLLOW_type_in_quantifier1785);
			type176=type();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, type176.getTree());

			string_literal177=(Token)match(input,DOUBLECOLON,FOLLOW_DOUBLECOLON_in_quantifier1787); if (state.failed) return retval;
			pushFollow(FOLLOW_expression_in_quantifier1790);
			expression178=expression();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, expression178.getTree());

			char_literal179=(Token)match(input,60,FOLLOW_60_in_quantifier1792); if (state.failed) return retval;
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
		// Dafny.g:190:5: ( ID ':=' 'call' )
		// Dafny.g:190:6: ID ':=' 'call'
		{
		match(input,ID,FOLLOW_ID_in_synpred1_Dafny1115); if (state.failed) return;

		match(input,ASSIGN,FOLLOW_ASSIGN_in_synpred1_Dafny1117); if (state.failed) return;

		match(input,CALL,FOLLOW_CALL_in_synpred1_Dafny1119); if (state.failed) return;

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



	public static final BitSet FOLLOW_LABEL_in_label547 = new BitSet(new long[]{0x0000000010000000L});
	public static final BitSet FOLLOW_ID_in_label550 = new BitSet(new long[]{0x4000000000000000L});
	public static final BitSet FOLLOW_62_in_label552 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_method_in_program566 = new BitSet(new long[]{0x0000021001000002L});
	public static final BitSet FOLLOW_function_in_program570 = new BitSet(new long[]{0x0000021001000002L});
	public static final BitSet FOLLOW_METHOD_in_method589 = new BitSet(new long[]{0x0000000010000000L});
	public static final BitSet FOLLOW_LEMMA_in_method593 = new BitSet(new long[]{0x0000000010000000L});
	public static final BitSet FOLLOW_ID_in_method598 = new BitSet(new long[]{0x0800000000000000L});
	public static final BitSet FOLLOW_59_in_method600 = new BitSet(new long[]{0x1000000010000000L});
	public static final BitSet FOLLOW_vars_in_method602 = new BitSet(new long[]{0x1000000000000000L});
	public static final BitSet FOLLOW_60_in_method605 = new BitSet(new long[]{0x0002800000224000L});
	public static final BitSet FOLLOW_returns__in_method611 = new BitSet(new long[]{0x0000800000224000L});
	public static final BitSet FOLLOW_requires_in_method620 = new BitSet(new long[]{0x0000800000224000L});
	public static final BitSet FOLLOW_ensures_in_method629 = new BitSet(new long[]{0x0000000000224000L});
	public static final BitSet FOLLOW_decreases_in_method638 = new BitSet(new long[]{0x0000000000004000L});
	public static final BitSet FOLLOW_BLOCK_BEGIN_in_method645 = new BitSet(new long[]{0x0300000430009400L});
	public static final BitSet FOLLOW_statements_in_method647 = new BitSet(new long[]{0x0000000000008000L});
	public static final BitSet FOLLOW_BLOCK_END_in_method650 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_FUNCTION_in_function712 = new BitSet(new long[]{0x0000000010000000L});
	public static final BitSet FOLLOW_ID_in_function717 = new BitSet(new long[]{0x0800000000000000L});
	public static final BitSet FOLLOW_59_in_function719 = new BitSet(new long[]{0x1000000010000000L});
	public static final BitSet FOLLOW_vars_in_function722 = new BitSet(new long[]{0x1000000000000000L});
	public static final BitSet FOLLOW_60_in_function725 = new BitSet(new long[]{0x4000000000000000L});
	public static final BitSet FOLLOW_62_in_function728 = new BitSet(new long[]{0x0004000080000080L});
	public static final BitSet FOLLOW_type_in_function731 = new BitSet(new long[]{0x0000000000004000L});
	public static final BitSet FOLLOW_BLOCK_BEGIN_in_function735 = new BitSet(new long[]{0x0800148010004000L,0x0000000000000001L});
	public static final BitSet FOLLOW_expression_in_function738 = new BitSet(new long[]{0x0000000000008000L});
	public static final BitSet FOLLOW_BLOCK_END_in_function740 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_var_in_vars753 = new BitSet(new long[]{0x2000000000000002L});
	public static final BitSet FOLLOW_61_in_vars759 = new BitSet(new long[]{0x0000000010000000L});
	public static final BitSet FOLLOW_var_in_vars762 = new BitSet(new long[]{0x2000000000000002L});
	public static final BitSet FOLLOW_ID_in_var777 = new BitSet(new long[]{0x4000000000000000L});
	public static final BitSet FOLLOW_62_in_var779 = new BitSet(new long[]{0x0004000080000080L});
	public static final BitSet FOLLOW_type_in_var781 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_INT_in_type805 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_SET_in_type809 = new BitSet(new long[]{0x0000010000000000L});
	public static final BitSet FOLLOW_LT_in_type812 = new BitSet(new long[]{0x0000000080000000L});
	public static final BitSet FOLLOW_INT_in_type815 = new BitSet(new long[]{0x0000000004000000L});
	public static final BitSet FOLLOW_GT_in_type817 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_ARRAY_in_type824 = new BitSet(new long[]{0x0000010000000000L});
	public static final BitSet FOLLOW_LT_in_type827 = new BitSet(new long[]{0x0000000080000000L});
	public static final BitSet FOLLOW_INT_in_type830 = new BitSet(new long[]{0x0000000004000000L});
	public static final BitSet FOLLOW_GT_in_type832 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_RETURNS_in_returns_845 = new BitSet(new long[]{0x0800000000000000L});
	public static final BitSet FOLLOW_59_in_returns_848 = new BitSet(new long[]{0x0000000010000000L});
	public static final BitSet FOLLOW_vars_in_returns_851 = new BitSet(new long[]{0x1000000000000000L});
	public static final BitSet FOLLOW_60_in_returns_853 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_REQUIRES_in_requires866 = new BitSet(new long[]{0x0800148410004000L,0x0000000000000001L});
	public static final BitSet FOLLOW_label_in_requires869 = new BitSet(new long[]{0x0800148010004000L,0x0000000000000001L});
	public static final BitSet FOLLOW_expression_in_requires872 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_ENSURES_in_ensures884 = new BitSet(new long[]{0x0800148410004000L,0x0000000000000001L});
	public static final BitSet FOLLOW_label_in_ensures887 = new BitSet(new long[]{0x0800148010004000L,0x0000000000000001L});
	public static final BitSet FOLLOW_expression_in_ensures890 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_DECREASES_in_decreases902 = new BitSet(new long[]{0x0800148010004000L,0x0000000000000001L});
	public static final BitSet FOLLOW_expression_in_decreases905 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_INVARIANT_in_invariant917 = new BitSet(new long[]{0x0800148410004000L,0x0000000000000001L});
	public static final BitSet FOLLOW_label_in_invariant920 = new BitSet(new long[]{0x0800148010004000L,0x0000000000000001L});
	public static final BitSet FOLLOW_expression_in_invariant923 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_BLOCK_BEGIN_in_block935 = new BitSet(new long[]{0x0300000430009400L});
	public static final BitSet FOLLOW_statements_in_block937 = new BitSet(new long[]{0x0000000000008000L});
	public static final BitSet FOLLOW_BLOCK_END_in_block940 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_block_in_relaxedBlock963 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_statement_in_relaxedBlock969 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_statement_in_statements991 = new BitSet(new long[]{0x0300000430001402L});
	public static final BitSet FOLLOW_VAR_in_statement1008 = new BitSet(new long[]{0x0000000010000000L});
	public static final BitSet FOLLOW_ID_in_statement1011 = new BitSet(new long[]{0x4000000000000000L});
	public static final BitSet FOLLOW_62_in_statement1013 = new BitSet(new long[]{0x0004000080000080L});
	public static final BitSet FOLLOW_type_in_statement1016 = new BitSet(new long[]{0x8000000000000800L});
	public static final BitSet FOLLOW_ASSIGN_in_statement1019 = new BitSet(new long[]{0x0800148010004000L,0x0000000000000001L});
	public static final BitSet FOLLOW_expression_in_statement1022 = new BitSet(new long[]{0x8000000000000000L});
	public static final BitSet FOLLOW_63_in_statement1026 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_ID_in_statement1033 = new BitSet(new long[]{0x0000000000000800L});
	public static final BitSet FOLLOW_ASSIGN_in_statement1035 = new BitSet(new long[]{0x0040000000000000L});
	public static final BitSet FOLLOW_TIMES_in_statement1037 = new BitSet(new long[]{0x8000000000000000L});
	public static final BitSet FOLLOW_63_in_statement1039 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_ID_in_statement1053 = new BitSet(new long[]{0x0000000000000800L});
	public static final BitSet FOLLOW_ASSIGN_in_statement1055 = new BitSet(new long[]{0x0800148010004000L,0x0000000000000001L});
	public static final BitSet FOLLOW_expression_in_statement1058 = new BitSet(new long[]{0x8000000000000000L});
	public static final BitSet FOLLOW_63_in_statement1060 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_ID_in_statement1067 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000001L});
	public static final BitSet FOLLOW_64_in_statement1069 = new BitSet(new long[]{0x0800148010004000L,0x0000000000000001L});
	public static final BitSet FOLLOW_expression_in_statement1073 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000002L});
	public static final BitSet FOLLOW_65_in_statement1075 = new BitSet(new long[]{0x0000000000000800L});
	public static final BitSet FOLLOW_ASSIGN_in_statement1079 = new BitSet(new long[]{0x0800148010004000L,0x0000000000000001L});
	public static final BitSet FOLLOW_expression_in_statement1083 = new BitSet(new long[]{0x8000000000000000L});
	public static final BitSet FOLLOW_63_in_statement1085 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_ID_in_statement1126 = new BitSet(new long[]{0x0000000000000800L});
	public static final BitSet FOLLOW_ASSIGN_in_statement1128 = new BitSet(new long[]{0x0000000000010000L});
	public static final BitSet FOLLOW_CALL_in_statement1130 = new BitSet(new long[]{0x0000000010000000L});
	public static final BitSet FOLLOW_ID_in_statement1134 = new BitSet(new long[]{0x0800000000000000L});
	public static final BitSet FOLLOW_59_in_statement1136 = new BitSet(new long[]{0x1800148010004000L,0x0000000000000001L});
	public static final BitSet FOLLOW_expressions_in_statement1138 = new BitSet(new long[]{0x1000000000000000L});
	public static final BitSet FOLLOW_60_in_statement1141 = new BitSet(new long[]{0x8000000000000000L});
	public static final BitSet FOLLOW_63_in_statement1143 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_ids_in_statement1180 = new BitSet(new long[]{0x0000000000000800L});
	public static final BitSet FOLLOW_ASSIGN_in_statement1182 = new BitSet(new long[]{0x0000000000010000L});
	public static final BitSet FOLLOW_CALL_in_statement1184 = new BitSet(new long[]{0x0000000010000000L});
	public static final BitSet FOLLOW_ID_in_statement1186 = new BitSet(new long[]{0x0800000000000000L});
	public static final BitSet FOLLOW_59_in_statement1188 = new BitSet(new long[]{0x1800148010004000L,0x0000000000000001L});
	public static final BitSet FOLLOW_expressions_in_statement1190 = new BitSet(new long[]{0x1000000000000000L});
	public static final BitSet FOLLOW_60_in_statement1193 = new BitSet(new long[]{0x8000000000000000L});
	public static final BitSet FOLLOW_63_in_statement1195 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_label_in_statement1230 = new BitSet(new long[]{0x0200000000000000L});
	public static final BitSet FOLLOW_WHILE_in_statement1239 = new BitSet(new long[]{0x0800148010004000L,0x0000000000000001L});
	public static final BitSet FOLLOW_expression_in_statement1241 = new BitSet(new long[]{0x0000000200000000L});
	public static final BitSet FOLLOW_invariant_in_statement1243 = new BitSet(new long[]{0x0000000200020000L});
	public static final BitSet FOLLOW_decreases_in_statement1246 = new BitSet(new long[]{0x0300000430005400L});
	public static final BitSet FOLLOW_relaxedBlock_in_statement1248 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_label_in_statement1280 = new BitSet(new long[]{0x0000000020000000L});
	public static final BitSet FOLLOW_IF_in_statement1283 = new BitSet(new long[]{0x0800148010004000L,0x0000000000000001L});
	public static final BitSet FOLLOW_expression_in_statement1286 = new BitSet(new long[]{0x0300000430005400L});
	public static final BitSet FOLLOW_relaxedBlock_in_statement1288 = new BitSet(new long[]{0x0000000000100002L});
	public static final BitSet FOLLOW_ELSE_in_statement1309 = new BitSet(new long[]{0x0300000430005400L});
	public static final BitSet FOLLOW_relaxedBlock_in_statement1312 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_ASSERT_in_statement1321 = new BitSet(new long[]{0x0800148410004000L,0x0000000000000001L});
	public static final BitSet FOLLOW_LABEL_in_statement1326 = new BitSet(new long[]{0x0000000010000000L});
	public static final BitSet FOLLOW_ID_in_statement1329 = new BitSet(new long[]{0x4000000000000000L});
	public static final BitSet FOLLOW_62_in_statement1331 = new BitSet(new long[]{0x0800148010004000L,0x0000000000000001L});
	public static final BitSet FOLLOW_expression_in_statement1337 = new BitSet(new long[]{0x8000000000000000L});
	public static final BitSet FOLLOW_63_in_statement1339 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_ASSUME_in_statement1346 = new BitSet(new long[]{0x0800148410004000L,0x0000000000000001L});
	public static final BitSet FOLLOW_LABEL_in_statement1351 = new BitSet(new long[]{0x0000000010000000L});
	public static final BitSet FOLLOW_ID_in_statement1354 = new BitSet(new long[]{0x4000000000000000L});
	public static final BitSet FOLLOW_62_in_statement1356 = new BitSet(new long[]{0x0800148010004000L,0x0000000000000001L});
	public static final BitSet FOLLOW_expression_in_statement1362 = new BitSet(new long[]{0x8000000000000000L});
	public static final BitSet FOLLOW_63_in_statement1364 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_ID_in_ids1377 = new BitSet(new long[]{0x2000000000000000L});
	public static final BitSet FOLLOW_61_in_ids1380 = new BitSet(new long[]{0x0000000010000000L});
	public static final BitSet FOLLOW_ID_in_ids1383 = new BitSet(new long[]{0x2000000000000002L});
	public static final BitSet FOLLOW_expression_in_expressions1397 = new BitSet(new long[]{0x2000000000000002L});
	public static final BitSet FOLLOW_61_in_expressions1401 = new BitSet(new long[]{0x0800148010004000L,0x0000000000000001L});
	public static final BitSet FOLLOW_expression_in_expressions1404 = new BitSet(new long[]{0x2000000000000002L});
	public static final BitSet FOLLOW_or_expr_in_expression1419 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_and_expr_in_or_expr1428 = new BitSet(new long[]{0x0000200040000002L});
	public static final BitSet FOLLOW_OR_in_or_expr1433 = new BitSet(new long[]{0x0800148010004000L,0x0000000000000001L});
	public static final BitSet FOLLOW_IMPLIES_in_or_expr1438 = new BitSet(new long[]{0x0800148010004000L,0x0000000000000001L});
	public static final BitSet FOLLOW_or_expr_in_or_expr1442 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_rel_expr_in_and_expr1457 = new BitSet(new long[]{0x0000000000000022L});
	public static final BitSet FOLLOW_AND_in_and_expr1461 = new BitSet(new long[]{0x0800148010004000L,0x0000000000000001L});
	public static final BitSet FOLLOW_and_expr_in_and_expr1464 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_add_expr_in_rel_expr1479 = new BitSet(new long[]{0x0000010806400002L});
	public static final BitSet FOLLOW_LT_in_rel_expr1484 = new BitSet(new long[]{0x0800148010004000L,0x0000000000000001L});
	public static final BitSet FOLLOW_GT_in_rel_expr1489 = new BitSet(new long[]{0x0800148010004000L,0x0000000000000001L});
	public static final BitSet FOLLOW_EQ_in_rel_expr1494 = new BitSet(new long[]{0x0800148010004000L,0x0000000000000001L});
	public static final BitSet FOLLOW_LE_in_rel_expr1499 = new BitSet(new long[]{0x0800148010004000L,0x0000000000000001L});
	public static final BitSet FOLLOW_GE_in_rel_expr1504 = new BitSet(new long[]{0x0800148010004000L,0x0000000000000001L});
	public static final BitSet FOLLOW_add_expr_in_rel_expr1508 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_mul_expr_in_add_expr1523 = new BitSet(new long[]{0x0080440000000002L});
	public static final BitSet FOLLOW_set_in_add_expr1527 = new BitSet(new long[]{0x0800148010004000L,0x0000000000000001L});
	public static final BitSet FOLLOW_add_expr_in_add_expr1540 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_prefix_expr_in_mul_expr1555 = new BitSet(new long[]{0x0040000100000002L});
	public static final BitSet FOLLOW_set_in_mul_expr1559 = new BitSet(new long[]{0x0800148010004000L,0x0000000000000001L});
	public static final BitSet FOLLOW_mul_expr_in_mul_expr1568 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_MINUS_in_prefix_expr1585 = new BitSet(new long[]{0x0800148010004000L,0x0000000000000001L});
	public static final BitSet FOLLOW_prefix_expr_in_prefix_expr1588 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_NOT_in_prefix_expr1594 = new BitSet(new long[]{0x0800148010004000L,0x0000000000000001L});
	public static final BitSet FOLLOW_prefix_expr_in_prefix_expr1597 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_postfix_expr_in_prefix_expr1603 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_atom_expr_in_postfix_expr1615 = new BitSet(new long[]{0x0000000000040002L,0x0000000000000001L});
	public static final BitSet FOLLOW_64_in_postfix_expr1621 = new BitSet(new long[]{0x0800148010004000L,0x0000000000000001L});
	public static final BitSet FOLLOW_expression_in_postfix_expr1623 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000002L});
	public static final BitSet FOLLOW_65_in_postfix_expr1625 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_DOT_in_postfix_expr1643 = new BitSet(new long[]{0x0000002000000000L});
	public static final BitSet FOLLOW_LENGTH_in_postfix_expr1645 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_EOF_in_postfix_expr1669 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_ID_in_atom_expr1691 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_LIT_in_atom_expr1697 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_quantifier_in_atom_expr1703 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_59_in_atom_expr1709 = new BitSet(new long[]{0x0800148010004000L,0x0000000000000001L});
	public static final BitSet FOLLOW_expression_in_atom_expr1712 = new BitSet(new long[]{0x1000000000000000L});
	public static final BitSet FOLLOW_60_in_atom_expr1714 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_BLOCK_BEGIN_in_atom_expr1721 = new BitSet(new long[]{0x080014801000C000L,0x0000000000000001L});
	public static final BitSet FOLLOW_expressions_in_atom_expr1723 = new BitSet(new long[]{0x0000000000008000L});
	public static final BitSet FOLLOW_BLOCK_END_in_atom_expr1726 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_64_in_atom_expr1741 = new BitSet(new long[]{0x0800148010004000L,0x0000000000000003L});
	public static final BitSet FOLLOW_expressions_in_atom_expr1743 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000002L});
	public static final BitSet FOLLOW_65_in_atom_expr1746 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_59_in_quantifier1767 = new BitSet(new long[]{0x0000000000800010L});
	public static final BitSet FOLLOW_ALL_in_quantifier1771 = new BitSet(new long[]{0x0000000010000000L});
	public static final BitSet FOLLOW_EX_in_quantifier1776 = new BitSet(new long[]{0x0000000010000000L});
	public static final BitSet FOLLOW_ID_in_quantifier1780 = new BitSet(new long[]{0x4000000000000000L});
	public static final BitSet FOLLOW_62_in_quantifier1782 = new BitSet(new long[]{0x0004000080000080L});
	public static final BitSet FOLLOW_type_in_quantifier1785 = new BitSet(new long[]{0x0000000000080000L});
	public static final BitSet FOLLOW_DOUBLECOLON_in_quantifier1787 = new BitSet(new long[]{0x0800148010004000L,0x0000000000000001L});
	public static final BitSet FOLLOW_expression_in_quantifier1790 = new BitSet(new long[]{0x1000000000000000L});
	public static final BitSet FOLLOW_60_in_quantifier1792 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_ID_in_synpred1_Dafny1115 = new BitSet(new long[]{0x0000000000000800L});
	public static final BitSet FOLLOW_ASSIGN_in_synpred1_Dafny1117 = new BitSet(new long[]{0x0000000000010000L});
	public static final BitSet FOLLOW_CALL_in_synpred1_Dafny1119 = new BitSet(new long[]{0x0000000000000002L});
}
