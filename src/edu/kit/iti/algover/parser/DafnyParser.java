// $ANTLR 3.5.1 Dafny.g 2015-09-22 14:47:18

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
	// Dafny.g:115:1: method : tok= ( 'method' | 'lemma' ) ID '(' ( vars )? ')' ( returns_ )? ( requires )* ( ensures )* ( decreases )? '{' ( decl )* ( statements )? '}' -> ^( METHOD[tok] ID ^( ARGS ( vars )? ) ( returns_ )? ( requires )* ( ensures )* ( decreases )? ( decl )* ^( BLOCK ( statements )? ) ) ;
	public final DafnyParser.method_return method() throws RecognitionException {
		DafnyParser.method_return retval = new DafnyParser.method_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		Token tok=null;
		Token ID6=null;
		Token char_literal7=null;
		Token char_literal9=null;
		Token char_literal14=null;
		Token char_literal17=null;
		ParserRuleReturnScope vars8 =null;
		ParserRuleReturnScope returns_10 =null;
		ParserRuleReturnScope requires11 =null;
		ParserRuleReturnScope ensures12 =null;
		ParserRuleReturnScope decreases13 =null;
		ParserRuleReturnScope decl15 =null;
		ParserRuleReturnScope statements16 =null;

		DafnyTree tok_tree=null;
		DafnyTree ID6_tree=null;
		DafnyTree char_literal7_tree=null;
		DafnyTree char_literal9_tree=null;
		DafnyTree char_literal14_tree=null;
		DafnyTree char_literal17_tree=null;
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
		RewriteRuleSubtreeStream stream_decl=new RewriteRuleSubtreeStream(adaptor,"rule decl");

		try {
			// Dafny.g:115:7: (tok= ( 'method' | 'lemma' ) ID '(' ( vars )? ')' ( returns_ )? ( requires )* ( ensures )* ( decreases )? '{' ( decl )* ( statements )? '}' -> ^( METHOD[tok] ID ^( ARGS ( vars )? ) ( returns_ )? ( requires )* ( ensures )* ( decreases )? ( decl )* ^( BLOCK ( statements )? ) ) )
			// Dafny.g:116:3: tok= ( 'method' | 'lemma' ) ID '(' ( vars )? ')' ( returns_ )? ( requires )* ( ensures )* ( decreases )? '{' ( decl )* ( statements )? '}'
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

			// Dafny.g:122:7: ( decl )*
			loop8:
			while (true) {
				int alt8=2;
				int LA8_0 = input.LA(1);
				if ( (LA8_0==VAR) ) {
					alt8=1;
				}

				switch (alt8) {
				case 1 :
					// Dafny.g:122:9: decl
					{
					pushFollow(FOLLOW_decl_in_method631);
					decl15=decl();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_decl.add(decl15.getTree());
					}
					break;

				default :
					break loop8;
				}
			}

			// Dafny.g:122:17: ( statements )?
			int alt9=2;
			int LA9_0 = input.LA(1);
			if ( (LA9_0==ASSERT||(LA9_0 >= ID && LA9_0 <= IF)||LA9_0==LABEL||LA9_0==WHILE) ) {
				alt9=1;
			}
			switch (alt9) {
				case 1 :
					// Dafny.g:122:17: statements
					{
					pushFollow(FOLLOW_statements_in_method636);
					statements16=statements();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_statements.add(statements16.getTree());
					}
					break;

			}

			char_literal17=(Token)match(input,BLOCK_END,FOLLOW_BLOCK_END_in_method639); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_BLOCK_END.add(char_literal17);

			// AST REWRITE
			// elements: returns_, decreases, vars, ID, decl, requires, statements, ensures
			// token labels: 
			// rule labels: retval
			// token list labels: 
			// rule list labels: 
			// wildcard labels: 
			if ( state.backtracking==0 ) {
			retval.tree = root_0;
			RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

			root_0 = (DafnyTree)adaptor.nil();
			// 123:3: -> ^( METHOD[tok] ID ^( ARGS ( vars )? ) ( returns_ )? ( requires )* ( ensures )* ( decreases )? ( decl )* ^( BLOCK ( statements )? ) )
			{
				// Dafny.g:124:5: ^( METHOD[tok] ID ^( ARGS ( vars )? ) ( returns_ )? ( requires )* ( ensures )* ( decreases )? ( decl )* ^( BLOCK ( statements )? ) )
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

				// Dafny.g:125:20: ( decl )*
				while ( stream_decl.hasNext() ) {
					adaptor.addChild(root_1, stream_decl.nextTree());
				}
				stream_decl.reset();

				// Dafny.g:125:26: ^( BLOCK ( statements )? )
				{
				DafnyTree root_2 = (DafnyTree)adaptor.nil();
				root_2 = (DafnyTree)adaptor.becomeRoot((DafnyTree)adaptor.create(BLOCK, "BLOCK"), root_2);
				// Dafny.g:125:34: ( statements )?
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

		Token string_literal18=null;
		Token ID19=null;
		Token char_literal20=null;
		Token char_literal22=null;
		Token char_literal23=null;
		Token char_literal25=null;
		Token char_literal27=null;
		ParserRuleReturnScope vars21 =null;
		ParserRuleReturnScope type24 =null;
		ParserRuleReturnScope expression26 =null;

		DafnyTree string_literal18_tree=null;
		DafnyTree ID19_tree=null;
		DafnyTree char_literal20_tree=null;
		DafnyTree char_literal22_tree=null;
		DafnyTree char_literal23_tree=null;
		DafnyTree char_literal25_tree=null;
		DafnyTree char_literal27_tree=null;

		try {
			// Dafny.g:128:9: ( 'function' ^ ID '(' ! ( vars )? ')' ! ':' ! type '{' ! expression '}' !)
			// Dafny.g:129:3: 'function' ^ ID '(' ! ( vars )? ')' ! ':' ! type '{' ! expression '}' !
			{
			root_0 = (DafnyTree)adaptor.nil();


			string_literal18=(Token)match(input,FUNCTION,FOLLOW_FUNCTION_in_function704); if (state.failed) return retval;
			if ( state.backtracking==0 ) {
			string_literal18_tree = (DafnyTree)adaptor.create(string_literal18);
			root_0 = (DafnyTree)adaptor.becomeRoot(string_literal18_tree, root_0);
			}

			ID19=(Token)match(input,ID,FOLLOW_ID_in_function709); if (state.failed) return retval;
			if ( state.backtracking==0 ) {
			ID19_tree = (DafnyTree)adaptor.create(ID19);
			adaptor.addChild(root_0, ID19_tree);
			}

			char_literal20=(Token)match(input,56,FOLLOW_56_in_function711); if (state.failed) return retval;
			// Dafny.g:130:11: ( vars )?
			int alt10=2;
			int LA10_0 = input.LA(1);
			if ( (LA10_0==ID) ) {
				alt10=1;
			}
			switch (alt10) {
				case 1 :
					// Dafny.g:130:11: vars
					{
					pushFollow(FOLLOW_vars_in_function714);
					vars21=vars();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, vars21.getTree());

					}
					break;

			}

			char_literal22=(Token)match(input,57,FOLLOW_57_in_function717); if (state.failed) return retval;
			char_literal23=(Token)match(input,59,FOLLOW_59_in_function720); if (state.failed) return retval;
			pushFollow(FOLLOW_type_in_function723);
			type24=type();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, type24.getTree());

			char_literal25=(Token)match(input,BLOCK_BEGIN,FOLLOW_BLOCK_BEGIN_in_function727); if (state.failed) return retval;
			pushFollow(FOLLOW_expression_in_function730);
			expression26=expression();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, expression26.getTree());

			char_literal27=(Token)match(input,BLOCK_END,FOLLOW_BLOCK_END_in_function732); if (state.failed) return retval;
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


	public static class decl_return extends ParserRuleReturnScope {
		DafnyTree tree;
		@Override
		public DafnyTree getTree() { return tree; }
	};


	// $ANTLR start "decl"
	// Dafny.g:134:1: decl : VAR ! var ';' !;
	public final DafnyParser.decl_return decl() throws RecognitionException {
		DafnyParser.decl_return retval = new DafnyParser.decl_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		Token VAR28=null;
		Token char_literal30=null;
		ParserRuleReturnScope var29 =null;

		DafnyTree VAR28_tree=null;
		DafnyTree char_literal30_tree=null;

		try {
			// Dafny.g:134:5: ( VAR ! var ';' !)
			// Dafny.g:135:3: VAR ! var ';' !
			{
			root_0 = (DafnyTree)adaptor.nil();


			VAR28=(Token)match(input,VAR,FOLLOW_VAR_in_decl745); if (state.failed) return retval;
			pushFollow(FOLLOW_var_in_decl748);
			var29=var();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, var29.getTree());

			char_literal30=(Token)match(input,60,FOLLOW_60_in_decl750); if (state.failed) return retval;
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
	// Dafny.g:138:1: vars : var ( ',' ! var )* ;
	public final DafnyParser.vars_return vars() throws RecognitionException {
		DafnyParser.vars_return retval = new DafnyParser.vars_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		Token char_literal32=null;
		ParserRuleReturnScope var31 =null;
		ParserRuleReturnScope var33 =null;

		DafnyTree char_literal32_tree=null;

		try {
			// Dafny.g:138:5: ( var ( ',' ! var )* )
			// Dafny.g:139:3: var ( ',' ! var )*
			{
			root_0 = (DafnyTree)adaptor.nil();


			pushFollow(FOLLOW_var_in_vars763);
			var31=var();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, var31.getTree());

			// Dafny.g:140:3: ( ',' ! var )*
			loop11:
			while (true) {
				int alt11=2;
				int LA11_0 = input.LA(1);
				if ( (LA11_0==58) ) {
					alt11=1;
				}

				switch (alt11) {
				case 1 :
					// Dafny.g:140:5: ',' ! var
					{
					char_literal32=(Token)match(input,58,FOLLOW_58_in_vars769); if (state.failed) return retval;
					pushFollow(FOLLOW_var_in_vars772);
					var33=var();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, var33.getTree());

					}
					break;

				default :
					break loop11;
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
	// Dafny.g:143:1: var : ID ':' type -> ^( VAR ID type ) ;
	public final DafnyParser.var_return var() throws RecognitionException {
		DafnyParser.var_return retval = new DafnyParser.var_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		Token ID34=null;
		Token char_literal35=null;
		ParserRuleReturnScope type36 =null;

		DafnyTree ID34_tree=null;
		DafnyTree char_literal35_tree=null;
		RewriteRuleTokenStream stream_59=new RewriteRuleTokenStream(adaptor,"token 59");
		RewriteRuleTokenStream stream_ID=new RewriteRuleTokenStream(adaptor,"token ID");
		RewriteRuleSubtreeStream stream_type=new RewriteRuleSubtreeStream(adaptor,"rule type");

		try {
			// Dafny.g:143:4: ( ID ':' type -> ^( VAR ID type ) )
			// Dafny.g:144:3: ID ':' type
			{
			ID34=(Token)match(input,ID,FOLLOW_ID_in_var787); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_ID.add(ID34);

			char_literal35=(Token)match(input,59,FOLLOW_59_in_var789); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_59.add(char_literal35);

			pushFollow(FOLLOW_type_in_var791);
			type36=type();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) stream_type.add(type36.getTree());
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
			// 144:15: -> ^( VAR ID type )
			{
				// Dafny.g:144:18: ^( VAR ID type )
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
	// Dafny.g:147:1: type : ( INT | SET ^ '<' ! INT '>' !| ARRAY ^ '<' ! INT '>' !);
	public final DafnyParser.type_return type() throws RecognitionException {
		DafnyParser.type_return retval = new DafnyParser.type_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		Token INT37=null;
		Token SET38=null;
		Token char_literal39=null;
		Token INT40=null;
		Token char_literal41=null;
		Token ARRAY42=null;
		Token char_literal43=null;
		Token INT44=null;
		Token char_literal45=null;

		DafnyTree INT37_tree=null;
		DafnyTree SET38_tree=null;
		DafnyTree char_literal39_tree=null;
		DafnyTree INT40_tree=null;
		DafnyTree char_literal41_tree=null;
		DafnyTree ARRAY42_tree=null;
		DafnyTree char_literal43_tree=null;
		DafnyTree INT44_tree=null;
		DafnyTree char_literal45_tree=null;

		try {
			// Dafny.g:147:5: ( INT | SET ^ '<' ! INT '>' !| ARRAY ^ '<' ! INT '>' !)
			int alt12=3;
			switch ( input.LA(1) ) {
			case INT:
				{
				alt12=1;
				}
				break;
			case SET:
				{
				alt12=2;
				}
				break;
			case ARRAY:
				{
				alt12=3;
				}
				break;
			default:
				if (state.backtracking>0) {state.failed=true; return retval;}
				NoViableAltException nvae =
					new NoViableAltException("", 12, 0, input);
				throw nvae;
			}
			switch (alt12) {
				case 1 :
					// Dafny.g:148:5: INT
					{
					root_0 = (DafnyTree)adaptor.nil();


					INT37=(Token)match(input,INT,FOLLOW_INT_in_type815); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					INT37_tree = (DafnyTree)adaptor.create(INT37);
					adaptor.addChild(root_0, INT37_tree);
					}

					}
					break;
				case 2 :
					// Dafny.g:148:11: SET ^ '<' ! INT '>' !
					{
					root_0 = (DafnyTree)adaptor.nil();


					SET38=(Token)match(input,SET,FOLLOW_SET_in_type819); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					SET38_tree = (DafnyTree)adaptor.create(SET38);
					root_0 = (DafnyTree)adaptor.becomeRoot(SET38_tree, root_0);
					}

					char_literal39=(Token)match(input,LT,FOLLOW_LT_in_type822); if (state.failed) return retval;
					INT40=(Token)match(input,INT,FOLLOW_INT_in_type825); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					INT40_tree = (DafnyTree)adaptor.create(INT40);
					adaptor.addChild(root_0, INT40_tree);
					}

					char_literal41=(Token)match(input,GT,FOLLOW_GT_in_type827); if (state.failed) return retval;
					}
					break;
				case 3 :
					// Dafny.g:149:5: ARRAY ^ '<' ! INT '>' !
					{
					root_0 = (DafnyTree)adaptor.nil();


					ARRAY42=(Token)match(input,ARRAY,FOLLOW_ARRAY_in_type834); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					ARRAY42_tree = (DafnyTree)adaptor.create(ARRAY42);
					root_0 = (DafnyTree)adaptor.becomeRoot(ARRAY42_tree, root_0);
					}

					char_literal43=(Token)match(input,LT,FOLLOW_LT_in_type837); if (state.failed) return retval;
					INT44=(Token)match(input,INT,FOLLOW_INT_in_type840); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					INT44_tree = (DafnyTree)adaptor.create(INT44);
					adaptor.addChild(root_0, INT44_tree);
					}

					char_literal45=(Token)match(input,GT,FOLLOW_GT_in_type842); if (state.failed) return retval;
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
	// Dafny.g:152:1: returns_ : RETURNS ^ '(' ! vars ')' !;
	public final DafnyParser.returns__return returns_() throws RecognitionException {
		DafnyParser.returns__return retval = new DafnyParser.returns__return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		Token RETURNS46=null;
		Token char_literal47=null;
		Token char_literal49=null;
		ParserRuleReturnScope vars48 =null;

		DafnyTree RETURNS46_tree=null;
		DafnyTree char_literal47_tree=null;
		DafnyTree char_literal49_tree=null;

		try {
			// Dafny.g:152:9: ( RETURNS ^ '(' ! vars ')' !)
			// Dafny.g:153:3: RETURNS ^ '(' ! vars ')' !
			{
			root_0 = (DafnyTree)adaptor.nil();


			RETURNS46=(Token)match(input,RETURNS,FOLLOW_RETURNS_in_returns_855); if (state.failed) return retval;
			if ( state.backtracking==0 ) {
			RETURNS46_tree = (DafnyTree)adaptor.create(RETURNS46);
			root_0 = (DafnyTree)adaptor.becomeRoot(RETURNS46_tree, root_0);
			}

			char_literal47=(Token)match(input,56,FOLLOW_56_in_returns_858); if (state.failed) return retval;
			pushFollow(FOLLOW_vars_in_returns_861);
			vars48=vars();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, vars48.getTree());

			char_literal49=(Token)match(input,57,FOLLOW_57_in_returns_863); if (state.failed) return retval;
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
	// Dafny.g:156:1: requires : REQUIRES ^ ( label )? expression ;
	public final DafnyParser.requires_return requires() throws RecognitionException {
		DafnyParser.requires_return retval = new DafnyParser.requires_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		Token REQUIRES50=null;
		ParserRuleReturnScope label51 =null;
		ParserRuleReturnScope expression52 =null;

		DafnyTree REQUIRES50_tree=null;

		try {
			// Dafny.g:156:9: ( REQUIRES ^ ( label )? expression )
			// Dafny.g:157:3: REQUIRES ^ ( label )? expression
			{
			root_0 = (DafnyTree)adaptor.nil();


			REQUIRES50=(Token)match(input,REQUIRES,FOLLOW_REQUIRES_in_requires876); if (state.failed) return retval;
			if ( state.backtracking==0 ) {
			REQUIRES50_tree = (DafnyTree)adaptor.create(REQUIRES50);
			root_0 = (DafnyTree)adaptor.becomeRoot(REQUIRES50_tree, root_0);
			}

			// Dafny.g:157:13: ( label )?
			int alt13=2;
			int LA13_0 = input.LA(1);
			if ( (LA13_0==LABEL) ) {
				alt13=1;
			}
			switch (alt13) {
				case 1 :
					// Dafny.g:157:13: label
					{
					pushFollow(FOLLOW_label_in_requires879);
					label51=label();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, label51.getTree());

					}
					break;

			}

			pushFollow(FOLLOW_expression_in_requires882);
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
	// $ANTLR end "requires"


	public static class ensures_return extends ParserRuleReturnScope {
		DafnyTree tree;
		@Override
		public DafnyTree getTree() { return tree; }
	};


	// $ANTLR start "ensures"
	// Dafny.g:160:1: ensures : ENSURES ^ ( label )? expression ;
	public final DafnyParser.ensures_return ensures() throws RecognitionException {
		DafnyParser.ensures_return retval = new DafnyParser.ensures_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		Token ENSURES53=null;
		ParserRuleReturnScope label54 =null;
		ParserRuleReturnScope expression55 =null;

		DafnyTree ENSURES53_tree=null;

		try {
			// Dafny.g:160:8: ( ENSURES ^ ( label )? expression )
			// Dafny.g:161:3: ENSURES ^ ( label )? expression
			{
			root_0 = (DafnyTree)adaptor.nil();


			ENSURES53=(Token)match(input,ENSURES,FOLLOW_ENSURES_in_ensures894); if (state.failed) return retval;
			if ( state.backtracking==0 ) {
			ENSURES53_tree = (DafnyTree)adaptor.create(ENSURES53);
			root_0 = (DafnyTree)adaptor.becomeRoot(ENSURES53_tree, root_0);
			}

			// Dafny.g:161:12: ( label )?
			int alt14=2;
			int LA14_0 = input.LA(1);
			if ( (LA14_0==LABEL) ) {
				alt14=1;
			}
			switch (alt14) {
				case 1 :
					// Dafny.g:161:12: label
					{
					pushFollow(FOLLOW_label_in_ensures897);
					label54=label();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, label54.getTree());

					}
					break;

			}

			pushFollow(FOLLOW_expression_in_ensures900);
			expression55=expression();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, expression55.getTree());

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
	// Dafny.g:164:1: decreases : DECREASES ^ expression ;
	public final DafnyParser.decreases_return decreases() throws RecognitionException {
		DafnyParser.decreases_return retval = new DafnyParser.decreases_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		Token DECREASES56=null;
		ParserRuleReturnScope expression57 =null;

		DafnyTree DECREASES56_tree=null;

		try {
			// Dafny.g:164:10: ( DECREASES ^ expression )
			// Dafny.g:165:3: DECREASES ^ expression
			{
			root_0 = (DafnyTree)adaptor.nil();


			DECREASES56=(Token)match(input,DECREASES,FOLLOW_DECREASES_in_decreases912); if (state.failed) return retval;
			if ( state.backtracking==0 ) {
			DECREASES56_tree = (DafnyTree)adaptor.create(DECREASES56);
			root_0 = (DafnyTree)adaptor.becomeRoot(DECREASES56_tree, root_0);
			}

			pushFollow(FOLLOW_expression_in_decreases915);
			expression57=expression();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, expression57.getTree());

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
	// Dafny.g:168:1: invariant : INVARIANT ^ ( label )? expression ;
	public final DafnyParser.invariant_return invariant() throws RecognitionException {
		DafnyParser.invariant_return retval = new DafnyParser.invariant_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		Token INVARIANT58=null;
		ParserRuleReturnScope label59 =null;
		ParserRuleReturnScope expression60 =null;

		DafnyTree INVARIANT58_tree=null;

		try {
			// Dafny.g:168:10: ( INVARIANT ^ ( label )? expression )
			// Dafny.g:169:3: INVARIANT ^ ( label )? expression
			{
			root_0 = (DafnyTree)adaptor.nil();


			INVARIANT58=(Token)match(input,INVARIANT,FOLLOW_INVARIANT_in_invariant927); if (state.failed) return retval;
			if ( state.backtracking==0 ) {
			INVARIANT58_tree = (DafnyTree)adaptor.create(INVARIANT58);
			root_0 = (DafnyTree)adaptor.becomeRoot(INVARIANT58_tree, root_0);
			}

			// Dafny.g:169:14: ( label )?
			int alt15=2;
			int LA15_0 = input.LA(1);
			if ( (LA15_0==LABEL) ) {
				alt15=1;
			}
			switch (alt15) {
				case 1 :
					// Dafny.g:169:14: label
					{
					pushFollow(FOLLOW_label_in_invariant930);
					label59=label();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, label59.getTree());

					}
					break;

			}

			pushFollow(FOLLOW_expression_in_invariant933);
			expression60=expression();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, expression60.getTree());

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
	// Dafny.g:172:1: block : '{' ( statements )? '}' -> ^( BLOCK ( statements )? ) ;
	public final DafnyParser.block_return block() throws RecognitionException {
		DafnyParser.block_return retval = new DafnyParser.block_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		Token char_literal61=null;
		Token char_literal63=null;
		ParserRuleReturnScope statements62 =null;

		DafnyTree char_literal61_tree=null;
		DafnyTree char_literal63_tree=null;
		RewriteRuleTokenStream stream_BLOCK_BEGIN=new RewriteRuleTokenStream(adaptor,"token BLOCK_BEGIN");
		RewriteRuleTokenStream stream_BLOCK_END=new RewriteRuleTokenStream(adaptor,"token BLOCK_END");
		RewriteRuleSubtreeStream stream_statements=new RewriteRuleSubtreeStream(adaptor,"rule statements");

		try {
			// Dafny.g:172:6: ( '{' ( statements )? '}' -> ^( BLOCK ( statements )? ) )
			// Dafny.g:173:3: '{' ( statements )? '}'
			{
			char_literal61=(Token)match(input,BLOCK_BEGIN,FOLLOW_BLOCK_BEGIN_in_block945); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_BLOCK_BEGIN.add(char_literal61);

			// Dafny.g:173:7: ( statements )?
			int alt16=2;
			int LA16_0 = input.LA(1);
			if ( (LA16_0==ASSERT||(LA16_0 >= ID && LA16_0 <= IF)||LA16_0==LABEL||LA16_0==WHILE) ) {
				alt16=1;
			}
			switch (alt16) {
				case 1 :
					// Dafny.g:173:7: statements
					{
					pushFollow(FOLLOW_statements_in_block947);
					statements62=statements();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_statements.add(statements62.getTree());
					}
					break;

			}

			char_literal63=(Token)match(input,BLOCK_END,FOLLOW_BLOCK_END_in_block950); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_BLOCK_END.add(char_literal63);

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
			// 173:23: -> ^( BLOCK ( statements )? )
			{
				// Dafny.g:173:26: ^( BLOCK ( statements )? )
				{
				DafnyTree root_1 = (DafnyTree)adaptor.nil();
				root_1 = (DafnyTree)adaptor.becomeRoot((DafnyTree)adaptor.create(BLOCK, "BLOCK"), root_1);
				// Dafny.g:173:34: ( statements )?
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
	// Dafny.g:176:1: relaxedBlock : ( block | statement -> ^( BLOCK statement ) );
	public final DafnyParser.relaxedBlock_return relaxedBlock() throws RecognitionException {
		DafnyParser.relaxedBlock_return retval = new DafnyParser.relaxedBlock_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		ParserRuleReturnScope block64 =null;
		ParserRuleReturnScope statement65 =null;

		RewriteRuleSubtreeStream stream_statement=new RewriteRuleSubtreeStream(adaptor,"rule statement");

		try {
			// Dafny.g:176:13: ( block | statement -> ^( BLOCK statement ) )
			int alt17=2;
			int LA17_0 = input.LA(1);
			if ( (LA17_0==BLOCK_BEGIN) ) {
				alt17=1;
			}
			else if ( (LA17_0==ASSERT||(LA17_0 >= ID && LA17_0 <= IF)||LA17_0==LABEL||LA17_0==WHILE) ) {
				alt17=2;
			}

			else {
				if (state.backtracking>0) {state.failed=true; return retval;}
				NoViableAltException nvae =
					new NoViableAltException("", 17, 0, input);
				throw nvae;
			}

			switch (alt17) {
				case 1 :
					// Dafny.g:177:5: block
					{
					root_0 = (DafnyTree)adaptor.nil();


					pushFollow(FOLLOW_block_in_relaxedBlock973);
					block64=block();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, block64.getTree());

					}
					break;
				case 2 :
					// Dafny.g:178:5: statement
					{
					pushFollow(FOLLOW_statement_in_relaxedBlock979);
					statement65=statement();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_statement.add(statement65.getTree());
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
					// 178:15: -> ^( BLOCK statement )
					{
						// Dafny.g:178:18: ^( BLOCK statement )
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
	// Dafny.g:181:1: statements : ( statement )+ ;
	public final DafnyParser.statements_return statements() throws RecognitionException {
		DafnyParser.statements_return retval = new DafnyParser.statements_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		ParserRuleReturnScope statement66 =null;


		try {
			// Dafny.g:181:11: ( ( statement )+ )
			// Dafny.g:182:3: ( statement )+
			{
			root_0 = (DafnyTree)adaptor.nil();


			// Dafny.g:182:3: ( statement )+
			int cnt18=0;
			loop18:
			while (true) {
				int alt18=2;
				int LA18_0 = input.LA(1);
				if ( (LA18_0==ASSERT||(LA18_0 >= ID && LA18_0 <= IF)||LA18_0==LABEL||LA18_0==WHILE) ) {
					alt18=1;
				}

				switch (alt18) {
				case 1 :
					// Dafny.g:182:5: statement
					{
					pushFollow(FOLLOW_statement_in_statements1001);
					statement66=statement();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, statement66.getTree());

					}
					break;

				default :
					if ( cnt18 >= 1 ) break loop18;
					if (state.backtracking>0) {state.failed=true; return retval;}
					EarlyExitException eee = new EarlyExitException(18, input);
					throw eee;
				}
				cnt18++;
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
	// Dafny.g:185:1: statement : ( ID ':=' ^ expression ';' !| ( ID ':=' 'call' )=>r= ID ':=' 'call' f= ID '(' ( expressions )? ')' ';' -> ^( 'call' $f ^( RESULTS $r) ^( ARGS ( expressions )? ) ) | ids ':=' 'call' ID '(' ( expressions )? ')' ';' -> ^( 'call' ID ^( RESULTS ids ) ^( ARGS ( expressions )? ) ) | ( label )? 'while' expression ( invariant )+ decreases relaxedBlock -> ^( 'while' ( label )? expression ( invariant )+ decreases relaxedBlock ) | ( label )? 'if' ^ expression relaxedBlock ( options {greedy=true; } : 'else' ! relaxedBlock )? | 'assert' ^ ( 'label' ! ID ':' !)? expression ';' !);
	public final DafnyParser.statement_return statement() throws RecognitionException {
		DafnyParser.statement_return retval = new DafnyParser.statement_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		Token r=null;
		Token f=null;
		Token ID67=null;
		Token string_literal68=null;
		Token char_literal70=null;
		Token string_literal71=null;
		Token string_literal72=null;
		Token char_literal73=null;
		Token char_literal75=null;
		Token char_literal76=null;
		Token string_literal78=null;
		Token string_literal79=null;
		Token ID80=null;
		Token char_literal81=null;
		Token char_literal83=null;
		Token char_literal84=null;
		Token string_literal86=null;
		Token string_literal92=null;
		Token string_literal95=null;
		Token string_literal97=null;
		Token string_literal98=null;
		Token ID99=null;
		Token char_literal100=null;
		Token char_literal102=null;
		ParserRuleReturnScope expression69 =null;
		ParserRuleReturnScope expressions74 =null;
		ParserRuleReturnScope ids77 =null;
		ParserRuleReturnScope expressions82 =null;
		ParserRuleReturnScope label85 =null;
		ParserRuleReturnScope expression87 =null;
		ParserRuleReturnScope invariant88 =null;
		ParserRuleReturnScope decreases89 =null;
		ParserRuleReturnScope relaxedBlock90 =null;
		ParserRuleReturnScope label91 =null;
		ParserRuleReturnScope expression93 =null;
		ParserRuleReturnScope relaxedBlock94 =null;
		ParserRuleReturnScope relaxedBlock96 =null;
		ParserRuleReturnScope expression101 =null;

		DafnyTree r_tree=null;
		DafnyTree f_tree=null;
		DafnyTree ID67_tree=null;
		DafnyTree string_literal68_tree=null;
		DafnyTree char_literal70_tree=null;
		DafnyTree string_literal71_tree=null;
		DafnyTree string_literal72_tree=null;
		DafnyTree char_literal73_tree=null;
		DafnyTree char_literal75_tree=null;
		DafnyTree char_literal76_tree=null;
		DafnyTree string_literal78_tree=null;
		DafnyTree string_literal79_tree=null;
		DafnyTree ID80_tree=null;
		DafnyTree char_literal81_tree=null;
		DafnyTree char_literal83_tree=null;
		DafnyTree char_literal84_tree=null;
		DafnyTree string_literal86_tree=null;
		DafnyTree string_literal92_tree=null;
		DafnyTree string_literal95_tree=null;
		DafnyTree string_literal97_tree=null;
		DafnyTree string_literal98_tree=null;
		DafnyTree ID99_tree=null;
		DafnyTree char_literal100_tree=null;
		DafnyTree char_literal102_tree=null;
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
			// Dafny.g:185:10: ( ID ':=' ^ expression ';' !| ( ID ':=' 'call' )=>r= ID ':=' 'call' f= ID '(' ( expressions )? ')' ';' -> ^( 'call' $f ^( RESULTS $r) ^( ARGS ( expressions )? ) ) | ids ':=' 'call' ID '(' ( expressions )? ')' ';' -> ^( 'call' ID ^( RESULTS ids ) ^( ARGS ( expressions )? ) ) | ( label )? 'while' expression ( invariant )+ decreases relaxedBlock -> ^( 'while' ( label )? expression ( invariant )+ decreases relaxedBlock ) | ( label )? 'if' ^ expression relaxedBlock ( options {greedy=true; } : 'else' ! relaxedBlock )? | 'assert' ^ ( 'label' ! ID ':' !)? expression ';' !)
			int alt26=6;
			switch ( input.LA(1) ) {
			case ID:
				{
				int LA26_1 = input.LA(2);
				if ( (LA26_1==ASSIGN) ) {
					int LA26_6 = input.LA(3);
					if ( (LA26_6==CALL) && (synpred1_Dafny())) {
						alt26=2;
					}
					else if ( (LA26_6==BLOCK_BEGIN||LA26_6==ID||LA26_6==LIT||LA26_6==MINUS||LA26_6==NOT||LA26_6==56||LA26_6==61) ) {
						alt26=1;
					}

					else {
						if (state.backtracking>0) {state.failed=true; return retval;}
						int nvaeMark = input.mark();
						try {
							for (int nvaeConsume = 0; nvaeConsume < 3 - 1; nvaeConsume++) {
								input.consume();
							}
							NoViableAltException nvae =
								new NoViableAltException("", 26, 6, input);
							throw nvae;
						} finally {
							input.rewind(nvaeMark);
						}
					}

				}
				else if ( (LA26_1==58) ) {
					alt26=3;
				}

				else {
					if (state.backtracking>0) {state.failed=true; return retval;}
					int nvaeMark = input.mark();
					try {
						input.consume();
						NoViableAltException nvae =
							new NoViableAltException("", 26, 1, input);
						throw nvae;
					} finally {
						input.rewind(nvaeMark);
					}
				}

				}
				break;
			case LABEL:
				{
				int LA26_2 = input.LA(2);
				if ( (LA26_2==ID) ) {
					int LA26_8 = input.LA(3);
					if ( (LA26_8==59) ) {
						int LA26_11 = input.LA(4);
						if ( (LA26_11==WHILE) ) {
							alt26=4;
						}
						else if ( (LA26_11==IF) ) {
							alt26=5;
						}

						else {
							if (state.backtracking>0) {state.failed=true; return retval;}
							int nvaeMark = input.mark();
							try {
								for (int nvaeConsume = 0; nvaeConsume < 4 - 1; nvaeConsume++) {
									input.consume();
								}
								NoViableAltException nvae =
									new NoViableAltException("", 26, 11, input);
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
								new NoViableAltException("", 26, 8, input);
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
							new NoViableAltException("", 26, 2, input);
						throw nvae;
					} finally {
						input.rewind(nvaeMark);
					}
				}

				}
				break;
			case WHILE:
				{
				alt26=4;
				}
				break;
			case IF:
				{
				alt26=5;
				}
				break;
			case ASSERT:
				{
				alt26=6;
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
					// Dafny.g:186:5: ID ':=' ^ expression ';' !
					{
					root_0 = (DafnyTree)adaptor.nil();


					ID67=(Token)match(input,ID,FOLLOW_ID_in_statement1018); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					ID67_tree = (DafnyTree)adaptor.create(ID67);
					adaptor.addChild(root_0, ID67_tree);
					}

					string_literal68=(Token)match(input,ASSIGN,FOLLOW_ASSIGN_in_statement1020); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					string_literal68_tree = (DafnyTree)adaptor.create(string_literal68);
					root_0 = (DafnyTree)adaptor.becomeRoot(string_literal68_tree, root_0);
					}

					pushFollow(FOLLOW_expression_in_statement1023);
					expression69=expression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, expression69.getTree());

					char_literal70=(Token)match(input,60,FOLLOW_60_in_statement1025); if (state.failed) return retval;
					}
					break;
				case 2 :
					// Dafny.g:187:5: ( ID ':=' 'call' )=>r= ID ':=' 'call' f= ID '(' ( expressions )? ')' ';'
					{
					r=(Token)match(input,ID,FOLLOW_ID_in_statement1044); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_ID.add(r);

					string_literal71=(Token)match(input,ASSIGN,FOLLOW_ASSIGN_in_statement1046); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_ASSIGN.add(string_literal71);

					string_literal72=(Token)match(input,CALL,FOLLOW_CALL_in_statement1048); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_CALL.add(string_literal72);

					f=(Token)match(input,ID,FOLLOW_ID_in_statement1052); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_ID.add(f);

					char_literal73=(Token)match(input,56,FOLLOW_56_in_statement1054); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_56.add(char_literal73);

					// Dafny.g:187:51: ( expressions )?
					int alt19=2;
					int LA19_0 = input.LA(1);
					if ( (LA19_0==BLOCK_BEGIN||LA19_0==ID||LA19_0==LIT||LA19_0==MINUS||LA19_0==NOT||LA19_0==56||LA19_0==61) ) {
						alt19=1;
					}
					switch (alt19) {
						case 1 :
							// Dafny.g:187:51: expressions
							{
							pushFollow(FOLLOW_expressions_in_statement1056);
							expressions74=expressions();
							state._fsp--;
							if (state.failed) return retval;
							if ( state.backtracking==0 ) stream_expressions.add(expressions74.getTree());
							}
							break;

					}

					char_literal75=(Token)match(input,57,FOLLOW_57_in_statement1059); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_57.add(char_literal75);

					char_literal76=(Token)match(input,60,FOLLOW_60_in_statement1061); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_60.add(char_literal76);

					// AST REWRITE
					// elements: expressions, r, f, CALL
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
					// 188:9: -> ^( 'call' $f ^( RESULTS $r) ^( ARGS ( expressions )? ) )
					{
						// Dafny.g:188:12: ^( 'call' $f ^( RESULTS $r) ^( ARGS ( expressions )? ) )
						{
						DafnyTree root_1 = (DafnyTree)adaptor.nil();
						root_1 = (DafnyTree)adaptor.becomeRoot(stream_CALL.nextNode(), root_1);
						adaptor.addChild(root_1, stream_f.nextNode());
						// Dafny.g:188:24: ^( RESULTS $r)
						{
						DafnyTree root_2 = (DafnyTree)adaptor.nil();
						root_2 = (DafnyTree)adaptor.becomeRoot((DafnyTree)adaptor.create(RESULTS, "RESULTS"), root_2);
						adaptor.addChild(root_2, stream_r.nextNode());
						adaptor.addChild(root_1, root_2);
						}

						// Dafny.g:188:38: ^( ARGS ( expressions )? )
						{
						DafnyTree root_2 = (DafnyTree)adaptor.nil();
						root_2 = (DafnyTree)adaptor.becomeRoot((DafnyTree)adaptor.create(ARGS, "ARGS"), root_2);
						// Dafny.g:188:45: ( expressions )?
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
					// Dafny.g:189:5: ids ':=' 'call' ID '(' ( expressions )? ')' ';'
					{
					pushFollow(FOLLOW_ids_in_statement1098);
					ids77=ids();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_ids.add(ids77.getTree());
					string_literal78=(Token)match(input,ASSIGN,FOLLOW_ASSIGN_in_statement1100); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_ASSIGN.add(string_literal78);

					string_literal79=(Token)match(input,CALL,FOLLOW_CALL_in_statement1102); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_CALL.add(string_literal79);

					ID80=(Token)match(input,ID,FOLLOW_ID_in_statement1104); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_ID.add(ID80);

					char_literal81=(Token)match(input,56,FOLLOW_56_in_statement1106); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_56.add(char_literal81);

					// Dafny.g:189:28: ( expressions )?
					int alt20=2;
					int LA20_0 = input.LA(1);
					if ( (LA20_0==BLOCK_BEGIN||LA20_0==ID||LA20_0==LIT||LA20_0==MINUS||LA20_0==NOT||LA20_0==56||LA20_0==61) ) {
						alt20=1;
					}
					switch (alt20) {
						case 1 :
							// Dafny.g:189:28: expressions
							{
							pushFollow(FOLLOW_expressions_in_statement1108);
							expressions82=expressions();
							state._fsp--;
							if (state.failed) return retval;
							if ( state.backtracking==0 ) stream_expressions.add(expressions82.getTree());
							}
							break;

					}

					char_literal83=(Token)match(input,57,FOLLOW_57_in_statement1111); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_57.add(char_literal83);

					char_literal84=(Token)match(input,60,FOLLOW_60_in_statement1113); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_60.add(char_literal84);

					// AST REWRITE
					// elements: CALL, ID, expressions, ids
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (DafnyTree)adaptor.nil();
					// 190:9: -> ^( 'call' ID ^( RESULTS ids ) ^( ARGS ( expressions )? ) )
					{
						// Dafny.g:190:12: ^( 'call' ID ^( RESULTS ids ) ^( ARGS ( expressions )? ) )
						{
						DafnyTree root_1 = (DafnyTree)adaptor.nil();
						root_1 = (DafnyTree)adaptor.becomeRoot(stream_CALL.nextNode(), root_1);
						adaptor.addChild(root_1, stream_ID.nextNode());
						// Dafny.g:190:24: ^( RESULTS ids )
						{
						DafnyTree root_2 = (DafnyTree)adaptor.nil();
						root_2 = (DafnyTree)adaptor.becomeRoot((DafnyTree)adaptor.create(RESULTS, "RESULTS"), root_2);
						adaptor.addChild(root_2, stream_ids.nextTree());
						adaptor.addChild(root_1, root_2);
						}

						// Dafny.g:190:39: ^( ARGS ( expressions )? )
						{
						DafnyTree root_2 = (DafnyTree)adaptor.nil();
						root_2 = (DafnyTree)adaptor.becomeRoot((DafnyTree)adaptor.create(ARGS, "ARGS"), root_2);
						// Dafny.g:190:46: ( expressions )?
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
					// Dafny.g:191:5: ( label )? 'while' expression ( invariant )+ decreases relaxedBlock
					{
					// Dafny.g:191:5: ( label )?
					int alt21=2;
					int LA21_0 = input.LA(1);
					if ( (LA21_0==LABEL) ) {
						alt21=1;
					}
					switch (alt21) {
						case 1 :
							// Dafny.g:191:5: label
							{
							pushFollow(FOLLOW_label_in_statement1148);
							label85=label();
							state._fsp--;
							if (state.failed) return retval;
							if ( state.backtracking==0 ) stream_label.add(label85.getTree());
							}
							break;

					}

					string_literal86=(Token)match(input,WHILE,FOLLOW_WHILE_in_statement1157); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_WHILE.add(string_literal86);

					pushFollow(FOLLOW_expression_in_statement1159);
					expression87=expression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_expression.add(expression87.getTree());
					// Dafny.g:192:26: ( invariant )+
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
							// Dafny.g:192:26: invariant
							{
							pushFollow(FOLLOW_invariant_in_statement1161);
							invariant88=invariant();
							state._fsp--;
							if (state.failed) return retval;
							if ( state.backtracking==0 ) stream_invariant.add(invariant88.getTree());
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

					pushFollow(FOLLOW_decreases_in_statement1164);
					decreases89=decreases();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_decreases.add(decreases89.getTree());
					pushFollow(FOLLOW_relaxedBlock_in_statement1166);
					relaxedBlock90=relaxedBlock();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_relaxedBlock.add(relaxedBlock90.getTree());
					// AST REWRITE
					// elements: WHILE, expression, label, decreases, invariant, relaxedBlock
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (DafnyTree)adaptor.nil();
					// 193:9: -> ^( 'while' ( label )? expression ( invariant )+ decreases relaxedBlock )
					{
						// Dafny.g:193:12: ^( 'while' ( label )? expression ( invariant )+ decreases relaxedBlock )
						{
						DafnyTree root_1 = (DafnyTree)adaptor.nil();
						root_1 = (DafnyTree)adaptor.becomeRoot(stream_WHILE.nextNode(), root_1);
						// Dafny.g:193:22: ( label )?
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
				case 5 :
					// Dafny.g:194:5: ( label )? 'if' ^ expression relaxedBlock ( options {greedy=true; } : 'else' ! relaxedBlock )?
					{
					root_0 = (DafnyTree)adaptor.nil();


					// Dafny.g:194:5: ( label )?
					int alt23=2;
					int LA23_0 = input.LA(1);
					if ( (LA23_0==LABEL) ) {
						alt23=1;
					}
					switch (alt23) {
						case 1 :
							// Dafny.g:194:5: label
							{
							pushFollow(FOLLOW_label_in_statement1198);
							label91=label();
							state._fsp--;
							if (state.failed) return retval;
							if ( state.backtracking==0 ) adaptor.addChild(root_0, label91.getTree());

							}
							break;

					}

					string_literal92=(Token)match(input,IF,FOLLOW_IF_in_statement1201); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					string_literal92_tree = (DafnyTree)adaptor.create(string_literal92);
					root_0 = (DafnyTree)adaptor.becomeRoot(string_literal92_tree, root_0);
					}

					pushFollow(FOLLOW_expression_in_statement1204);
					expression93=expression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, expression93.getTree());

					pushFollow(FOLLOW_relaxedBlock_in_statement1206);
					relaxedBlock94=relaxedBlock();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, relaxedBlock94.getTree());

					// Dafny.g:195:7: ( options {greedy=true; } : 'else' ! relaxedBlock )?
					int alt24=2;
					int LA24_0 = input.LA(1);
					if ( (LA24_0==ELSE) ) {
						alt24=1;
					}
					switch (alt24) {
						case 1 :
							// Dafny.g:195:36: 'else' ! relaxedBlock
							{
							string_literal95=(Token)match(input,ELSE,FOLLOW_ELSE_in_statement1227); if (state.failed) return retval;
							pushFollow(FOLLOW_relaxedBlock_in_statement1230);
							relaxedBlock96=relaxedBlock();
							state._fsp--;
							if (state.failed) return retval;
							if ( state.backtracking==0 ) adaptor.addChild(root_0, relaxedBlock96.getTree());

							}
							break;

					}

					}
					break;
				case 6 :
					// Dafny.g:196:5: 'assert' ^ ( 'label' ! ID ':' !)? expression ';' !
					{
					root_0 = (DafnyTree)adaptor.nil();


					string_literal97=(Token)match(input,ASSERT,FOLLOW_ASSERT_in_statement1239); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					string_literal97_tree = (DafnyTree)adaptor.create(string_literal97);
					root_0 = (DafnyTree)adaptor.becomeRoot(string_literal97_tree, root_0);
					}

					// Dafny.g:196:15: ( 'label' ! ID ':' !)?
					int alt25=2;
					int LA25_0 = input.LA(1);
					if ( (LA25_0==LABEL) ) {
						alt25=1;
					}
					switch (alt25) {
						case 1 :
							// Dafny.g:196:17: 'label' ! ID ':' !
							{
							string_literal98=(Token)match(input,LABEL,FOLLOW_LABEL_in_statement1244); if (state.failed) return retval;
							ID99=(Token)match(input,ID,FOLLOW_ID_in_statement1247); if (state.failed) return retval;
							if ( state.backtracking==0 ) {
							ID99_tree = (DafnyTree)adaptor.create(ID99);
							adaptor.addChild(root_0, ID99_tree);
							}

							char_literal100=(Token)match(input,59,FOLLOW_59_in_statement1249); if (state.failed) return retval;
							}
							break;

					}

					pushFollow(FOLLOW_expression_in_statement1255);
					expression101=expression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, expression101.getTree());

					char_literal102=(Token)match(input,60,FOLLOW_60_in_statement1257); if (state.failed) return retval;
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
	// Dafny.g:199:1: ids : ID ( ',' ! ID )+ ;
	public final DafnyParser.ids_return ids() throws RecognitionException {
		DafnyParser.ids_return retval = new DafnyParser.ids_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		Token ID103=null;
		Token char_literal104=null;
		Token ID105=null;

		DafnyTree ID103_tree=null;
		DafnyTree char_literal104_tree=null;
		DafnyTree ID105_tree=null;

		try {
			// Dafny.g:199:4: ( ID ( ',' ! ID )+ )
			// Dafny.g:200:3: ID ( ',' ! ID )+
			{
			root_0 = (DafnyTree)adaptor.nil();


			ID103=(Token)match(input,ID,FOLLOW_ID_in_ids1270); if (state.failed) return retval;
			if ( state.backtracking==0 ) {
			ID103_tree = (DafnyTree)adaptor.create(ID103);
			adaptor.addChild(root_0, ID103_tree);
			}

			// Dafny.g:200:6: ( ',' ! ID )+
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
					// Dafny.g:200:7: ',' ! ID
					{
					char_literal104=(Token)match(input,58,FOLLOW_58_in_ids1273); if (state.failed) return retval;
					ID105=(Token)match(input,ID,FOLLOW_ID_in_ids1276); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					ID105_tree = (DafnyTree)adaptor.create(ID105);
					adaptor.addChild(root_0, ID105_tree);
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
	// Dafny.g:203:1: expressions : expression ( ',' ! expression )* ;
	public final DafnyParser.expressions_return expressions() throws RecognitionException {
		DafnyParser.expressions_return retval = new DafnyParser.expressions_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		Token char_literal107=null;
		ParserRuleReturnScope expression106 =null;
		ParserRuleReturnScope expression108 =null;

		DafnyTree char_literal107_tree=null;

		try {
			// Dafny.g:203:12: ( expression ( ',' ! expression )* )
			// Dafny.g:204:3: expression ( ',' ! expression )*
			{
			root_0 = (DafnyTree)adaptor.nil();


			pushFollow(FOLLOW_expression_in_expressions1290);
			expression106=expression();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, expression106.getTree());

			// Dafny.g:204:14: ( ',' ! expression )*
			loop28:
			while (true) {
				int alt28=2;
				int LA28_0 = input.LA(1);
				if ( (LA28_0==58) ) {
					alt28=1;
				}

				switch (alt28) {
				case 1 :
					// Dafny.g:204:16: ',' ! expression
					{
					char_literal107=(Token)match(input,58,FOLLOW_58_in_expressions1294); if (state.failed) return retval;
					pushFollow(FOLLOW_expression_in_expressions1297);
					expression108=expression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, expression108.getTree());

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
	// Dafny.g:207:1: expression : or_expr ;
	public final DafnyParser.expression_return expression() throws RecognitionException {
		DafnyParser.expression_return retval = new DafnyParser.expression_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		ParserRuleReturnScope or_expr109 =null;


		try {
			// Dafny.g:207:11: ( or_expr )
			// Dafny.g:208:3: or_expr
			{
			root_0 = (DafnyTree)adaptor.nil();


			pushFollow(FOLLOW_or_expr_in_expression1312);
			or_expr109=or_expr();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, or_expr109.getTree());

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
	// Dafny.g:210:1: or_expr : and_expr ( ( '||' ^| '==>' ^) or_expr )? ;
	public final DafnyParser.or_expr_return or_expr() throws RecognitionException {
		DafnyParser.or_expr_return retval = new DafnyParser.or_expr_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		Token string_literal111=null;
		Token string_literal112=null;
		ParserRuleReturnScope and_expr110 =null;
		ParserRuleReturnScope or_expr113 =null;

		DafnyTree string_literal111_tree=null;
		DafnyTree string_literal112_tree=null;

		try {
			// Dafny.g:210:8: ( and_expr ( ( '||' ^| '==>' ^) or_expr )? )
			// Dafny.g:211:3: and_expr ( ( '||' ^| '==>' ^) or_expr )?
			{
			root_0 = (DafnyTree)adaptor.nil();


			pushFollow(FOLLOW_and_expr_in_or_expr1321);
			and_expr110=and_expr();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, and_expr110.getTree());

			// Dafny.g:211:12: ( ( '||' ^| '==>' ^) or_expr )?
			int alt30=2;
			int LA30_0 = input.LA(1);
			if ( (LA30_0==IMPLIES||LA30_0==OR) ) {
				alt30=1;
			}
			switch (alt30) {
				case 1 :
					// Dafny.g:211:14: ( '||' ^| '==>' ^) or_expr
					{
					// Dafny.g:211:14: ( '||' ^| '==>' ^)
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
							// Dafny.g:211:15: '||' ^
							{
							string_literal111=(Token)match(input,OR,FOLLOW_OR_in_or_expr1326); if (state.failed) return retval;
							if ( state.backtracking==0 ) {
							string_literal111_tree = (DafnyTree)adaptor.create(string_literal111);
							root_0 = (DafnyTree)adaptor.becomeRoot(string_literal111_tree, root_0);
							}

							}
							break;
						case 2 :
							// Dafny.g:211:23: '==>' ^
							{
							string_literal112=(Token)match(input,IMPLIES,FOLLOW_IMPLIES_in_or_expr1331); if (state.failed) return retval;
							if ( state.backtracking==0 ) {
							string_literal112_tree = (DafnyTree)adaptor.create(string_literal112);
							root_0 = (DafnyTree)adaptor.becomeRoot(string_literal112_tree, root_0);
							}

							}
							break;

					}

					pushFollow(FOLLOW_or_expr_in_or_expr1335);
					or_expr113=or_expr();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, or_expr113.getTree());

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
	// Dafny.g:214:1: and_expr : rel_expr ( '&&' ^ and_expr )? ;
	public final DafnyParser.and_expr_return and_expr() throws RecognitionException {
		DafnyParser.and_expr_return retval = new DafnyParser.and_expr_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		Token string_literal115=null;
		ParserRuleReturnScope rel_expr114 =null;
		ParserRuleReturnScope and_expr116 =null;

		DafnyTree string_literal115_tree=null;

		try {
			// Dafny.g:214:9: ( rel_expr ( '&&' ^ and_expr )? )
			// Dafny.g:215:3: rel_expr ( '&&' ^ and_expr )?
			{
			root_0 = (DafnyTree)adaptor.nil();


			pushFollow(FOLLOW_rel_expr_in_and_expr1350);
			rel_expr114=rel_expr();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, rel_expr114.getTree());

			// Dafny.g:215:12: ( '&&' ^ and_expr )?
			int alt31=2;
			int LA31_0 = input.LA(1);
			if ( (LA31_0==AND) ) {
				alt31=1;
			}
			switch (alt31) {
				case 1 :
					// Dafny.g:215:14: '&&' ^ and_expr
					{
					string_literal115=(Token)match(input,AND,FOLLOW_AND_in_and_expr1354); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					string_literal115_tree = (DafnyTree)adaptor.create(string_literal115);
					root_0 = (DafnyTree)adaptor.becomeRoot(string_literal115_tree, root_0);
					}

					pushFollow(FOLLOW_and_expr_in_and_expr1357);
					and_expr116=and_expr();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, and_expr116.getTree());

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
	// Dafny.g:218:1: rel_expr : add_expr ( ( '<' ^| '>' ^| '==' ^| '<=' ^| '>=' ^) add_expr )? ;
	public final DafnyParser.rel_expr_return rel_expr() throws RecognitionException {
		DafnyParser.rel_expr_return retval = new DafnyParser.rel_expr_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		Token char_literal118=null;
		Token char_literal119=null;
		Token string_literal120=null;
		Token string_literal121=null;
		Token string_literal122=null;
		ParserRuleReturnScope add_expr117 =null;
		ParserRuleReturnScope add_expr123 =null;

		DafnyTree char_literal118_tree=null;
		DafnyTree char_literal119_tree=null;
		DafnyTree string_literal120_tree=null;
		DafnyTree string_literal121_tree=null;
		DafnyTree string_literal122_tree=null;

		try {
			// Dafny.g:218:9: ( add_expr ( ( '<' ^| '>' ^| '==' ^| '<=' ^| '>=' ^) add_expr )? )
			// Dafny.g:219:3: add_expr ( ( '<' ^| '>' ^| '==' ^| '<=' ^| '>=' ^) add_expr )?
			{
			root_0 = (DafnyTree)adaptor.nil();


			pushFollow(FOLLOW_add_expr_in_rel_expr1372);
			add_expr117=add_expr();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, add_expr117.getTree());

			// Dafny.g:219:12: ( ( '<' ^| '>' ^| '==' ^| '<=' ^| '>=' ^) add_expr )?
			int alt33=2;
			int LA33_0 = input.LA(1);
			if ( (LA33_0==EQ||(LA33_0 >= GE && LA33_0 <= GT)||LA33_0==LE||LA33_0==LT) ) {
				alt33=1;
			}
			switch (alt33) {
				case 1 :
					// Dafny.g:219:14: ( '<' ^| '>' ^| '==' ^| '<=' ^| '>=' ^) add_expr
					{
					// Dafny.g:219:14: ( '<' ^| '>' ^| '==' ^| '<=' ^| '>=' ^)
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
							// Dafny.g:219:15: '<' ^
							{
							char_literal118=(Token)match(input,LT,FOLLOW_LT_in_rel_expr1377); if (state.failed) return retval;
							if ( state.backtracking==0 ) {
							char_literal118_tree = (DafnyTree)adaptor.create(char_literal118);
							root_0 = (DafnyTree)adaptor.becomeRoot(char_literal118_tree, root_0);
							}

							}
							break;
						case 2 :
							// Dafny.g:219:22: '>' ^
							{
							char_literal119=(Token)match(input,GT,FOLLOW_GT_in_rel_expr1382); if (state.failed) return retval;
							if ( state.backtracking==0 ) {
							char_literal119_tree = (DafnyTree)adaptor.create(char_literal119);
							root_0 = (DafnyTree)adaptor.becomeRoot(char_literal119_tree, root_0);
							}

							}
							break;
						case 3 :
							// Dafny.g:219:29: '==' ^
							{
							string_literal120=(Token)match(input,EQ,FOLLOW_EQ_in_rel_expr1387); if (state.failed) return retval;
							if ( state.backtracking==0 ) {
							string_literal120_tree = (DafnyTree)adaptor.create(string_literal120);
							root_0 = (DafnyTree)adaptor.becomeRoot(string_literal120_tree, root_0);
							}

							}
							break;
						case 4 :
							// Dafny.g:219:37: '<=' ^
							{
							string_literal121=(Token)match(input,LE,FOLLOW_LE_in_rel_expr1392); if (state.failed) return retval;
							if ( state.backtracking==0 ) {
							string_literal121_tree = (DafnyTree)adaptor.create(string_literal121);
							root_0 = (DafnyTree)adaptor.becomeRoot(string_literal121_tree, root_0);
							}

							}
							break;
						case 5 :
							// Dafny.g:219:45: '>=' ^
							{
							string_literal122=(Token)match(input,GE,FOLLOW_GE_in_rel_expr1397); if (state.failed) return retval;
							if ( state.backtracking==0 ) {
							string_literal122_tree = (DafnyTree)adaptor.create(string_literal122);
							root_0 = (DafnyTree)adaptor.becomeRoot(string_literal122_tree, root_0);
							}

							}
							break;

					}

					pushFollow(FOLLOW_add_expr_in_rel_expr1401);
					add_expr123=add_expr();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, add_expr123.getTree());

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
	// Dafny.g:222:1: add_expr : mul_expr ( ( '+' | '-' | '++' ) ^ add_expr )? ;
	public final DafnyParser.add_expr_return add_expr() throws RecognitionException {
		DafnyParser.add_expr_return retval = new DafnyParser.add_expr_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		Token set125=null;
		ParserRuleReturnScope mul_expr124 =null;
		ParserRuleReturnScope add_expr126 =null;

		DafnyTree set125_tree=null;

		try {
			// Dafny.g:222:9: ( mul_expr ( ( '+' | '-' | '++' ) ^ add_expr )? )
			// Dafny.g:223:3: mul_expr ( ( '+' | '-' | '++' ) ^ add_expr )?
			{
			root_0 = (DafnyTree)adaptor.nil();


			pushFollow(FOLLOW_mul_expr_in_add_expr1416);
			mul_expr124=mul_expr();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, mul_expr124.getTree());

			// Dafny.g:223:12: ( ( '+' | '-' | '++' ) ^ add_expr )?
			int alt34=2;
			int LA34_0 = input.LA(1);
			if ( (LA34_0==MINUS||LA34_0==PLUS||LA34_0==UNION) ) {
				alt34=1;
			}
			switch (alt34) {
				case 1 :
					// Dafny.g:223:14: ( '+' | '-' | '++' ) ^ add_expr
					{
					set125=input.LT(1);
					set125=input.LT(1);
					if ( input.LA(1)==MINUS||input.LA(1)==PLUS||input.LA(1)==UNION ) {
						input.consume();
						if ( state.backtracking==0 ) root_0 = (DafnyTree)adaptor.becomeRoot((DafnyTree)adaptor.create(set125), root_0);
						state.errorRecovery=false;
						state.failed=false;
					}
					else {
						if (state.backtracking>0) {state.failed=true; return retval;}
						MismatchedSetException mse = new MismatchedSetException(null,input);
						throw mse;
					}
					pushFollow(FOLLOW_add_expr_in_add_expr1433);
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
	// $ANTLR end "add_expr"


	public static class mul_expr_return extends ParserRuleReturnScope {
		DafnyTree tree;
		@Override
		public DafnyTree getTree() { return tree; }
	};


	// $ANTLR start "mul_expr"
	// Dafny.g:226:1: mul_expr : prefix_expr ( ( '*' | '**' ) ^ mul_expr )? ;
	public final DafnyParser.mul_expr_return mul_expr() throws RecognitionException {
		DafnyParser.mul_expr_return retval = new DafnyParser.mul_expr_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		Token set128=null;
		ParserRuleReturnScope prefix_expr127 =null;
		ParserRuleReturnScope mul_expr129 =null;

		DafnyTree set128_tree=null;

		try {
			// Dafny.g:226:9: ( prefix_expr ( ( '*' | '**' ) ^ mul_expr )? )
			// Dafny.g:227:3: prefix_expr ( ( '*' | '**' ) ^ mul_expr )?
			{
			root_0 = (DafnyTree)adaptor.nil();


			pushFollow(FOLLOW_prefix_expr_in_mul_expr1448);
			prefix_expr127=prefix_expr();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, prefix_expr127.getTree());

			// Dafny.g:227:15: ( ( '*' | '**' ) ^ mul_expr )?
			int alt35=2;
			int LA35_0 = input.LA(1);
			if ( (LA35_0==INTERSECT||LA35_0==TIMES) ) {
				alt35=1;
			}
			switch (alt35) {
				case 1 :
					// Dafny.g:227:17: ( '*' | '**' ) ^ mul_expr
					{
					set128=input.LT(1);
					set128=input.LT(1);
					if ( input.LA(1)==INTERSECT||input.LA(1)==TIMES ) {
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
					pushFollow(FOLLOW_mul_expr_in_mul_expr1461);
					mul_expr129=mul_expr();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, mul_expr129.getTree());

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
	// Dafny.g:230:1: prefix_expr : ( '-' ^ prefix_expr | '!' ^ prefix_expr | postfix_expr );
	public final DafnyParser.prefix_expr_return prefix_expr() throws RecognitionException {
		DafnyParser.prefix_expr_return retval = new DafnyParser.prefix_expr_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		Token char_literal130=null;
		Token char_literal132=null;
		ParserRuleReturnScope prefix_expr131 =null;
		ParserRuleReturnScope prefix_expr133 =null;
		ParserRuleReturnScope postfix_expr134 =null;

		DafnyTree char_literal130_tree=null;
		DafnyTree char_literal132_tree=null;

		try {
			// Dafny.g:230:12: ( '-' ^ prefix_expr | '!' ^ prefix_expr | postfix_expr )
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
					// Dafny.g:231:5: '-' ^ prefix_expr
					{
					root_0 = (DafnyTree)adaptor.nil();


					char_literal130=(Token)match(input,MINUS,FOLLOW_MINUS_in_prefix_expr1478); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					char_literal130_tree = (DafnyTree)adaptor.create(char_literal130);
					root_0 = (DafnyTree)adaptor.becomeRoot(char_literal130_tree, root_0);
					}

					pushFollow(FOLLOW_prefix_expr_in_prefix_expr1481);
					prefix_expr131=prefix_expr();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, prefix_expr131.getTree());

					}
					break;
				case 2 :
					// Dafny.g:232:5: '!' ^ prefix_expr
					{
					root_0 = (DafnyTree)adaptor.nil();


					char_literal132=(Token)match(input,NOT,FOLLOW_NOT_in_prefix_expr1487); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					char_literal132_tree = (DafnyTree)adaptor.create(char_literal132);
					root_0 = (DafnyTree)adaptor.becomeRoot(char_literal132_tree, root_0);
					}

					pushFollow(FOLLOW_prefix_expr_in_prefix_expr1490);
					prefix_expr133=prefix_expr();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, prefix_expr133.getTree());

					}
					break;
				case 3 :
					// Dafny.g:233:5: postfix_expr
					{
					root_0 = (DafnyTree)adaptor.nil();


					pushFollow(FOLLOW_postfix_expr_in_prefix_expr1496);
					postfix_expr134=postfix_expr();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, postfix_expr134.getTree());

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
	// Dafny.g:236:1: postfix_expr : atom_expr ( '[' expression ']' -> ^( ARRAY_ACCESS atom_expr expression ) | '.' LENGTH -> ^( LENGTH atom_expr ) | -> atom_expr | EOF -> atom_expr ) ;
	public final DafnyParser.postfix_expr_return postfix_expr() throws RecognitionException {
		DafnyParser.postfix_expr_return retval = new DafnyParser.postfix_expr_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		Token char_literal136=null;
		Token char_literal138=null;
		Token char_literal139=null;
		Token LENGTH140=null;
		Token EOF141=null;
		ParserRuleReturnScope atom_expr135 =null;
		ParserRuleReturnScope expression137 =null;

		DafnyTree char_literal136_tree=null;
		DafnyTree char_literal138_tree=null;
		DafnyTree char_literal139_tree=null;
		DafnyTree LENGTH140_tree=null;
		DafnyTree EOF141_tree=null;
		RewriteRuleTokenStream stream_DOT=new RewriteRuleTokenStream(adaptor,"token DOT");
		RewriteRuleTokenStream stream_EOF=new RewriteRuleTokenStream(adaptor,"token EOF");
		RewriteRuleTokenStream stream_62=new RewriteRuleTokenStream(adaptor,"token 62");
		RewriteRuleTokenStream stream_LENGTH=new RewriteRuleTokenStream(adaptor,"token LENGTH");
		RewriteRuleTokenStream stream_61=new RewriteRuleTokenStream(adaptor,"token 61");
		RewriteRuleSubtreeStream stream_expression=new RewriteRuleSubtreeStream(adaptor,"rule expression");
		RewriteRuleSubtreeStream stream_atom_expr=new RewriteRuleSubtreeStream(adaptor,"rule atom_expr");

		try {
			// Dafny.g:236:13: ( atom_expr ( '[' expression ']' -> ^( ARRAY_ACCESS atom_expr expression ) | '.' LENGTH -> ^( LENGTH atom_expr ) | -> atom_expr | EOF -> atom_expr ) )
			// Dafny.g:237:3: atom_expr ( '[' expression ']' -> ^( ARRAY_ACCESS atom_expr expression ) | '.' LENGTH -> ^( LENGTH atom_expr ) | -> atom_expr | EOF -> atom_expr )
			{
			pushFollow(FOLLOW_atom_expr_in_postfix_expr1508);
			atom_expr135=atom_expr();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) stream_atom_expr.add(atom_expr135.getTree());
			// Dafny.g:238:3: ( '[' expression ']' -> ^( ARRAY_ACCESS atom_expr expression ) | '.' LENGTH -> ^( LENGTH atom_expr ) | -> atom_expr | EOF -> atom_expr )
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
					// Dafny.g:238:5: '[' expression ']'
					{
					char_literal136=(Token)match(input,61,FOLLOW_61_in_postfix_expr1514); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_61.add(char_literal136);

					pushFollow(FOLLOW_expression_in_postfix_expr1516);
					expression137=expression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_expression.add(expression137.getTree());
					char_literal138=(Token)match(input,62,FOLLOW_62_in_postfix_expr1518); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_62.add(char_literal138);

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
					// 238:24: -> ^( ARRAY_ACCESS atom_expr expression )
					{
						// Dafny.g:238:27: ^( ARRAY_ACCESS atom_expr expression )
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
					// Dafny.g:239:5: '.' LENGTH
					{
					char_literal139=(Token)match(input,DOT,FOLLOW_DOT_in_postfix_expr1536); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_DOT.add(char_literal139);

					LENGTH140=(Token)match(input,LENGTH,FOLLOW_LENGTH_in_postfix_expr1538); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_LENGTH.add(LENGTH140);

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
					// 239:16: -> ^( LENGTH atom_expr )
					{
						// Dafny.g:239:19: ^( LENGTH atom_expr )
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
					// Dafny.g:240:5: 
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
					// 240:5: -> atom_expr
					{
						adaptor.addChild(root_0, stream_atom_expr.nextTree());
					}


					retval.tree = root_0;
					}

					}
					break;
				case 4 :
					// Dafny.g:241:5: EOF
					{
					EOF141=(Token)match(input,EOF,FOLLOW_EOF_in_postfix_expr1562); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_EOF.add(EOF141);

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
					// 241:9: -> atom_expr
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
	// Dafny.g:245:1: atom_expr : ( ID | LIT | quantifier | '(' ! expression ')' !| '{' ( expressions )? '}' -> ^( SETEX ( expressions )? ) | '[' ( expressions )? ']' -> ^( LISTEX ( expressions )? ) );
	public final DafnyParser.atom_expr_return atom_expr() throws RecognitionException {
		DafnyParser.atom_expr_return retval = new DafnyParser.atom_expr_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		Token ID142=null;
		Token LIT143=null;
		Token char_literal145=null;
		Token char_literal147=null;
		Token char_literal148=null;
		Token char_literal150=null;
		Token char_literal151=null;
		Token char_literal153=null;
		ParserRuleReturnScope quantifier144 =null;
		ParserRuleReturnScope expression146 =null;
		ParserRuleReturnScope expressions149 =null;
		ParserRuleReturnScope expressions152 =null;

		DafnyTree ID142_tree=null;
		DafnyTree LIT143_tree=null;
		DafnyTree char_literal145_tree=null;
		DafnyTree char_literal147_tree=null;
		DafnyTree char_literal148_tree=null;
		DafnyTree char_literal150_tree=null;
		DafnyTree char_literal151_tree=null;
		DafnyTree char_literal153_tree=null;
		RewriteRuleTokenStream stream_62=new RewriteRuleTokenStream(adaptor,"token 62");
		RewriteRuleTokenStream stream_BLOCK_BEGIN=new RewriteRuleTokenStream(adaptor,"token BLOCK_BEGIN");
		RewriteRuleTokenStream stream_61=new RewriteRuleTokenStream(adaptor,"token 61");
		RewriteRuleTokenStream stream_BLOCK_END=new RewriteRuleTokenStream(adaptor,"token BLOCK_END");
		RewriteRuleSubtreeStream stream_expressions=new RewriteRuleSubtreeStream(adaptor,"rule expressions");

		try {
			// Dafny.g:245:10: ( ID | LIT | quantifier | '(' ! expression ')' !| '{' ( expressions )? '}' -> ^( SETEX ( expressions )? ) | '[' ( expressions )? ']' -> ^( LISTEX ( expressions )? ) )
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
					// Dafny.g:246:5: ID
					{
					root_0 = (DafnyTree)adaptor.nil();


					ID142=(Token)match(input,ID,FOLLOW_ID_in_atom_expr1584); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					ID142_tree = (DafnyTree)adaptor.create(ID142);
					adaptor.addChild(root_0, ID142_tree);
					}

					}
					break;
				case 2 :
					// Dafny.g:247:5: LIT
					{
					root_0 = (DafnyTree)adaptor.nil();


					LIT143=(Token)match(input,LIT,FOLLOW_LIT_in_atom_expr1590); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					LIT143_tree = (DafnyTree)adaptor.create(LIT143);
					adaptor.addChild(root_0, LIT143_tree);
					}

					}
					break;
				case 3 :
					// Dafny.g:248:5: quantifier
					{
					root_0 = (DafnyTree)adaptor.nil();


					pushFollow(FOLLOW_quantifier_in_atom_expr1596);
					quantifier144=quantifier();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, quantifier144.getTree());

					}
					break;
				case 4 :
					// Dafny.g:249:5: '(' ! expression ')' !
					{
					root_0 = (DafnyTree)adaptor.nil();


					char_literal145=(Token)match(input,56,FOLLOW_56_in_atom_expr1602); if (state.failed) return retval;
					pushFollow(FOLLOW_expression_in_atom_expr1605);
					expression146=expression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, expression146.getTree());

					char_literal147=(Token)match(input,57,FOLLOW_57_in_atom_expr1607); if (state.failed) return retval;
					}
					break;
				case 5 :
					// Dafny.g:250:5: '{' ( expressions )? '}'
					{
					char_literal148=(Token)match(input,BLOCK_BEGIN,FOLLOW_BLOCK_BEGIN_in_atom_expr1614); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_BLOCK_BEGIN.add(char_literal148);

					// Dafny.g:250:9: ( expressions )?
					int alt38=2;
					int LA38_0 = input.LA(1);
					if ( (LA38_0==BLOCK_BEGIN||LA38_0==ID||LA38_0==LIT||LA38_0==MINUS||LA38_0==NOT||LA38_0==56||LA38_0==61) ) {
						alt38=1;
					}
					switch (alt38) {
						case 1 :
							// Dafny.g:250:9: expressions
							{
							pushFollow(FOLLOW_expressions_in_atom_expr1616);
							expressions149=expressions();
							state._fsp--;
							if (state.failed) return retval;
							if ( state.backtracking==0 ) stream_expressions.add(expressions149.getTree());
							}
							break;

					}

					char_literal150=(Token)match(input,BLOCK_END,FOLLOW_BLOCK_END_in_atom_expr1619); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_BLOCK_END.add(char_literal150);

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
					// 250:26: -> ^( SETEX ( expressions )? )
					{
						// Dafny.g:250:29: ^( SETEX ( expressions )? )
						{
						DafnyTree root_1 = (DafnyTree)adaptor.nil();
						root_1 = (DafnyTree)adaptor.becomeRoot((DafnyTree)adaptor.create(SETEX, "SETEX"), root_1);
						// Dafny.g:250:37: ( expressions )?
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
					// Dafny.g:251:5: '[' ( expressions )? ']'
					{
					char_literal151=(Token)match(input,61,FOLLOW_61_in_atom_expr1634); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_61.add(char_literal151);

					// Dafny.g:251:9: ( expressions )?
					int alt39=2;
					int LA39_0 = input.LA(1);
					if ( (LA39_0==BLOCK_BEGIN||LA39_0==ID||LA39_0==LIT||LA39_0==MINUS||LA39_0==NOT||LA39_0==56||LA39_0==61) ) {
						alt39=1;
					}
					switch (alt39) {
						case 1 :
							// Dafny.g:251:9: expressions
							{
							pushFollow(FOLLOW_expressions_in_atom_expr1636);
							expressions152=expressions();
							state._fsp--;
							if (state.failed) return retval;
							if ( state.backtracking==0 ) stream_expressions.add(expressions152.getTree());
							}
							break;

					}

					char_literal153=(Token)match(input,62,FOLLOW_62_in_atom_expr1639); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_62.add(char_literal153);

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
					// 251:26: -> ^( LISTEX ( expressions )? )
					{
						// Dafny.g:251:29: ^( LISTEX ( expressions )? )
						{
						DafnyTree root_1 = (DafnyTree)adaptor.nil();
						root_1 = (DafnyTree)adaptor.becomeRoot((DafnyTree)adaptor.create(LISTEX, "LISTEX"), root_1);
						// Dafny.g:251:38: ( expressions )?
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
	// Dafny.g:254:1: quantifier : '(' ! ( ALL ^| EX ^) ID ':' ! type '::' ! expression ')' !;
	public final DafnyParser.quantifier_return quantifier() throws RecognitionException {
		DafnyParser.quantifier_return retval = new DafnyParser.quantifier_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		Token char_literal154=null;
		Token ALL155=null;
		Token EX156=null;
		Token ID157=null;
		Token char_literal158=null;
		Token string_literal160=null;
		Token char_literal162=null;
		ParserRuleReturnScope type159 =null;
		ParserRuleReturnScope expression161 =null;

		DafnyTree char_literal154_tree=null;
		DafnyTree ALL155_tree=null;
		DafnyTree EX156_tree=null;
		DafnyTree ID157_tree=null;
		DafnyTree char_literal158_tree=null;
		DafnyTree string_literal160_tree=null;
		DafnyTree char_literal162_tree=null;

		try {
			// Dafny.g:254:11: ( '(' ! ( ALL ^| EX ^) ID ':' ! type '::' ! expression ')' !)
			// Dafny.g:255:3: '(' ! ( ALL ^| EX ^) ID ':' ! type '::' ! expression ')' !
			{
			root_0 = (DafnyTree)adaptor.nil();


			char_literal154=(Token)match(input,56,FOLLOW_56_in_quantifier1660); if (state.failed) return retval;
			// Dafny.g:255:8: ( ALL ^| EX ^)
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
					// Dafny.g:255:9: ALL ^
					{
					ALL155=(Token)match(input,ALL,FOLLOW_ALL_in_quantifier1664); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					ALL155_tree = (DafnyTree)adaptor.create(ALL155);
					root_0 = (DafnyTree)adaptor.becomeRoot(ALL155_tree, root_0);
					}

					}
					break;
				case 2 :
					// Dafny.g:255:16: EX ^
					{
					EX156=(Token)match(input,EX,FOLLOW_EX_in_quantifier1669); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					EX156_tree = (DafnyTree)adaptor.create(EX156);
					root_0 = (DafnyTree)adaptor.becomeRoot(EX156_tree, root_0);
					}

					}
					break;

			}

			ID157=(Token)match(input,ID,FOLLOW_ID_in_quantifier1673); if (state.failed) return retval;
			if ( state.backtracking==0 ) {
			ID157_tree = (DafnyTree)adaptor.create(ID157);
			adaptor.addChild(root_0, ID157_tree);
			}

			char_literal158=(Token)match(input,59,FOLLOW_59_in_quantifier1675); if (state.failed) return retval;
			pushFollow(FOLLOW_type_in_quantifier1678);
			type159=type();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, type159.getTree());

			string_literal160=(Token)match(input,DOUBLECOLON,FOLLOW_DOUBLECOLON_in_quantifier1680); if (state.failed) return retval;
			pushFollow(FOLLOW_expression_in_quantifier1683);
			expression161=expression();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, expression161.getTree());

			char_literal162=(Token)match(input,57,FOLLOW_57_in_quantifier1685); if (state.failed) return retval;
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
		// Dafny.g:187:5: ( ID ':=' 'call' )
		// Dafny.g:187:6: ID ':=' 'call'
		{
		match(input,ID,FOLLOW_ID_in_synpred1_Dafny1033); if (state.failed) return;

		match(input,ASSIGN,FOLLOW_ASSIGN_in_synpred1_Dafny1035); if (state.failed) return;

		match(input,CALL,FOLLOW_CALL_in_synpred1_Dafny1037); if (state.failed) return;

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
	public static final BitSet FOLLOW_decl_in_method631 = new BitSet(new long[]{0x0060000086002200L});
	public static final BitSet FOLLOW_statements_in_method636 = new BitSet(new long[]{0x0000000000002000L});
	public static final BitSet FOLLOW_BLOCK_END_in_method639 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_FUNCTION_in_function704 = new BitSet(new long[]{0x0000000002000000L});
	public static final BitSet FOLLOW_ID_in_function709 = new BitSet(new long[]{0x0100000000000000L});
	public static final BitSet FOLLOW_56_in_function711 = new BitSet(new long[]{0x0200000002000000L});
	public static final BitSet FOLLOW_vars_in_function714 = new BitSet(new long[]{0x0200000000000000L});
	public static final BitSet FOLLOW_57_in_function717 = new BitSet(new long[]{0x0800000000000000L});
	public static final BitSet FOLLOW_59_in_function720 = new BitSet(new long[]{0x0000800010000080L});
	public static final BitSet FOLLOW_type_in_function723 = new BitSet(new long[]{0x0000000000001000L});
	public static final BitSet FOLLOW_BLOCK_BEGIN_in_function727 = new BitSet(new long[]{0x2100029002001000L});
	public static final BitSet FOLLOW_expression_in_function730 = new BitSet(new long[]{0x0000000000002000L});
	public static final BitSet FOLLOW_BLOCK_END_in_function732 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_VAR_in_decl745 = new BitSet(new long[]{0x0000000002000000L});
	public static final BitSet FOLLOW_var_in_decl748 = new BitSet(new long[]{0x1000000000000000L});
	public static final BitSet FOLLOW_60_in_decl750 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_var_in_vars763 = new BitSet(new long[]{0x0400000000000002L});
	public static final BitSet FOLLOW_58_in_vars769 = new BitSet(new long[]{0x0000000002000000L});
	public static final BitSet FOLLOW_var_in_vars772 = new BitSet(new long[]{0x0400000000000002L});
	public static final BitSet FOLLOW_ID_in_var787 = new BitSet(new long[]{0x0800000000000000L});
	public static final BitSet FOLLOW_59_in_var789 = new BitSet(new long[]{0x0000800010000080L});
	public static final BitSet FOLLOW_type_in_var791 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_INT_in_type815 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_SET_in_type819 = new BitSet(new long[]{0x0000002000000000L});
	public static final BitSet FOLLOW_LT_in_type822 = new BitSet(new long[]{0x0000000010000000L});
	public static final BitSet FOLLOW_INT_in_type825 = new BitSet(new long[]{0x0000000001000000L});
	public static final BitSet FOLLOW_GT_in_type827 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_ARRAY_in_type834 = new BitSet(new long[]{0x0000002000000000L});
	public static final BitSet FOLLOW_LT_in_type837 = new BitSet(new long[]{0x0000000010000000L});
	public static final BitSet FOLLOW_INT_in_type840 = new BitSet(new long[]{0x0000000001000000L});
	public static final BitSet FOLLOW_GT_in_type842 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_RETURNS_in_returns_855 = new BitSet(new long[]{0x0100000000000000L});
	public static final BitSet FOLLOW_56_in_returns_858 = new BitSet(new long[]{0x0000000002000000L});
	public static final BitSet FOLLOW_vars_in_returns_861 = new BitSet(new long[]{0x0200000000000000L});
	public static final BitSet FOLLOW_57_in_returns_863 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_REQUIRES_in_requires876 = new BitSet(new long[]{0x2100029082001000L});
	public static final BitSet FOLLOW_label_in_requires879 = new BitSet(new long[]{0x2100029002001000L});
	public static final BitSet FOLLOW_expression_in_requires882 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_ENSURES_in_ensures894 = new BitSet(new long[]{0x2100029082001000L});
	public static final BitSet FOLLOW_label_in_ensures897 = new BitSet(new long[]{0x2100029002001000L});
	public static final BitSet FOLLOW_expression_in_ensures900 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_DECREASES_in_decreases912 = new BitSet(new long[]{0x2100029002001000L});
	public static final BitSet FOLLOW_expression_in_decreases915 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_INVARIANT_in_invariant927 = new BitSet(new long[]{0x2100029082001000L});
	public static final BitSet FOLLOW_label_in_invariant930 = new BitSet(new long[]{0x2100029002001000L});
	public static final BitSet FOLLOW_expression_in_invariant933 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_BLOCK_BEGIN_in_block945 = new BitSet(new long[]{0x0040000086002200L});
	public static final BitSet FOLLOW_statements_in_block947 = new BitSet(new long[]{0x0000000000002000L});
	public static final BitSet FOLLOW_BLOCK_END_in_block950 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_block_in_relaxedBlock973 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_statement_in_relaxedBlock979 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_statement_in_statements1001 = new BitSet(new long[]{0x0040000086000202L});
	public static final BitSet FOLLOW_ID_in_statement1018 = new BitSet(new long[]{0x0000000000000400L});
	public static final BitSet FOLLOW_ASSIGN_in_statement1020 = new BitSet(new long[]{0x2100029002001000L});
	public static final BitSet FOLLOW_expression_in_statement1023 = new BitSet(new long[]{0x1000000000000000L});
	public static final BitSet FOLLOW_60_in_statement1025 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_ID_in_statement1044 = new BitSet(new long[]{0x0000000000000400L});
	public static final BitSet FOLLOW_ASSIGN_in_statement1046 = new BitSet(new long[]{0x0000000000004000L});
	public static final BitSet FOLLOW_CALL_in_statement1048 = new BitSet(new long[]{0x0000000002000000L});
	public static final BitSet FOLLOW_ID_in_statement1052 = new BitSet(new long[]{0x0100000000000000L});
	public static final BitSet FOLLOW_56_in_statement1054 = new BitSet(new long[]{0x2300029002001000L});
	public static final BitSet FOLLOW_expressions_in_statement1056 = new BitSet(new long[]{0x0200000000000000L});
	public static final BitSet FOLLOW_57_in_statement1059 = new BitSet(new long[]{0x1000000000000000L});
	public static final BitSet FOLLOW_60_in_statement1061 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_ids_in_statement1098 = new BitSet(new long[]{0x0000000000000400L});
	public static final BitSet FOLLOW_ASSIGN_in_statement1100 = new BitSet(new long[]{0x0000000000004000L});
	public static final BitSet FOLLOW_CALL_in_statement1102 = new BitSet(new long[]{0x0000000002000000L});
	public static final BitSet FOLLOW_ID_in_statement1104 = new BitSet(new long[]{0x0100000000000000L});
	public static final BitSet FOLLOW_56_in_statement1106 = new BitSet(new long[]{0x2300029002001000L});
	public static final BitSet FOLLOW_expressions_in_statement1108 = new BitSet(new long[]{0x0200000000000000L});
	public static final BitSet FOLLOW_57_in_statement1111 = new BitSet(new long[]{0x1000000000000000L});
	public static final BitSet FOLLOW_60_in_statement1113 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_label_in_statement1148 = new BitSet(new long[]{0x0040000000000000L});
	public static final BitSet FOLLOW_WHILE_in_statement1157 = new BitSet(new long[]{0x2100029002001000L});
	public static final BitSet FOLLOW_expression_in_statement1159 = new BitSet(new long[]{0x0000000040000000L});
	public static final BitSet FOLLOW_invariant_in_statement1161 = new BitSet(new long[]{0x0000000040008000L});
	public static final BitSet FOLLOW_decreases_in_statement1164 = new BitSet(new long[]{0x0040000086001200L});
	public static final BitSet FOLLOW_relaxedBlock_in_statement1166 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_label_in_statement1198 = new BitSet(new long[]{0x0000000004000000L});
	public static final BitSet FOLLOW_IF_in_statement1201 = new BitSet(new long[]{0x2100029002001000L});
	public static final BitSet FOLLOW_expression_in_statement1204 = new BitSet(new long[]{0x0040000086001200L});
	public static final BitSet FOLLOW_relaxedBlock_in_statement1206 = new BitSet(new long[]{0x0000000000040002L});
	public static final BitSet FOLLOW_ELSE_in_statement1227 = new BitSet(new long[]{0x0040000086001200L});
	public static final BitSet FOLLOW_relaxedBlock_in_statement1230 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_ASSERT_in_statement1239 = new BitSet(new long[]{0x2100029082001000L});
	public static final BitSet FOLLOW_LABEL_in_statement1244 = new BitSet(new long[]{0x0000000002000000L});
	public static final BitSet FOLLOW_ID_in_statement1247 = new BitSet(new long[]{0x0800000000000000L});
	public static final BitSet FOLLOW_59_in_statement1249 = new BitSet(new long[]{0x2100029002001000L});
	public static final BitSet FOLLOW_expression_in_statement1255 = new BitSet(new long[]{0x1000000000000000L});
	public static final BitSet FOLLOW_60_in_statement1257 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_ID_in_ids1270 = new BitSet(new long[]{0x0400000000000000L});
	public static final BitSet FOLLOW_58_in_ids1273 = new BitSet(new long[]{0x0000000002000000L});
	public static final BitSet FOLLOW_ID_in_ids1276 = new BitSet(new long[]{0x0400000000000002L});
	public static final BitSet FOLLOW_expression_in_expressions1290 = new BitSet(new long[]{0x0400000000000002L});
	public static final BitSet FOLLOW_58_in_expressions1294 = new BitSet(new long[]{0x2100029002001000L});
	public static final BitSet FOLLOW_expression_in_expressions1297 = new BitSet(new long[]{0x0400000000000002L});
	public static final BitSet FOLLOW_or_expr_in_expression1312 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_and_expr_in_or_expr1321 = new BitSet(new long[]{0x0000040008000002L});
	public static final BitSet FOLLOW_OR_in_or_expr1326 = new BitSet(new long[]{0x2100029002001000L});
	public static final BitSet FOLLOW_IMPLIES_in_or_expr1331 = new BitSet(new long[]{0x2100029002001000L});
	public static final BitSet FOLLOW_or_expr_in_or_expr1335 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_rel_expr_in_and_expr1350 = new BitSet(new long[]{0x0000000000000022L});
	public static final BitSet FOLLOW_AND_in_and_expr1354 = new BitSet(new long[]{0x2100029002001000L});
	public static final BitSet FOLLOW_and_expr_in_and_expr1357 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_add_expr_in_rel_expr1372 = new BitSet(new long[]{0x0000002101900002L});
	public static final BitSet FOLLOW_LT_in_rel_expr1377 = new BitSet(new long[]{0x2100029002001000L});
	public static final BitSet FOLLOW_GT_in_rel_expr1382 = new BitSet(new long[]{0x2100029002001000L});
	public static final BitSet FOLLOW_EQ_in_rel_expr1387 = new BitSet(new long[]{0x2100029002001000L});
	public static final BitSet FOLLOW_LE_in_rel_expr1392 = new BitSet(new long[]{0x2100029002001000L});
	public static final BitSet FOLLOW_GE_in_rel_expr1397 = new BitSet(new long[]{0x2100029002001000L});
	public static final BitSet FOLLOW_add_expr_in_rel_expr1401 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_mul_expr_in_add_expr1416 = new BitSet(new long[]{0x0010088000000002L});
	public static final BitSet FOLLOW_set_in_add_expr1420 = new BitSet(new long[]{0x2100029002001000L});
	public static final BitSet FOLLOW_add_expr_in_add_expr1433 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_prefix_expr_in_mul_expr1448 = new BitSet(new long[]{0x0008000020000002L});
	public static final BitSet FOLLOW_set_in_mul_expr1452 = new BitSet(new long[]{0x2100029002001000L});
	public static final BitSet FOLLOW_mul_expr_in_mul_expr1461 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_MINUS_in_prefix_expr1478 = new BitSet(new long[]{0x2100029002001000L});
	public static final BitSet FOLLOW_prefix_expr_in_prefix_expr1481 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_NOT_in_prefix_expr1487 = new BitSet(new long[]{0x2100029002001000L});
	public static final BitSet FOLLOW_prefix_expr_in_prefix_expr1490 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_postfix_expr_in_prefix_expr1496 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_atom_expr_in_postfix_expr1508 = new BitSet(new long[]{0x2000000000010002L});
	public static final BitSet FOLLOW_61_in_postfix_expr1514 = new BitSet(new long[]{0x2100029002001000L});
	public static final BitSet FOLLOW_expression_in_postfix_expr1516 = new BitSet(new long[]{0x4000000000000000L});
	public static final BitSet FOLLOW_62_in_postfix_expr1518 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_DOT_in_postfix_expr1536 = new BitSet(new long[]{0x0000000400000000L});
	public static final BitSet FOLLOW_LENGTH_in_postfix_expr1538 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_EOF_in_postfix_expr1562 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_ID_in_atom_expr1584 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_LIT_in_atom_expr1590 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_quantifier_in_atom_expr1596 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_56_in_atom_expr1602 = new BitSet(new long[]{0x2100029002001000L});
	public static final BitSet FOLLOW_expression_in_atom_expr1605 = new BitSet(new long[]{0x0200000000000000L});
	public static final BitSet FOLLOW_57_in_atom_expr1607 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_BLOCK_BEGIN_in_atom_expr1614 = new BitSet(new long[]{0x2100029002003000L});
	public static final BitSet FOLLOW_expressions_in_atom_expr1616 = new BitSet(new long[]{0x0000000000002000L});
	public static final BitSet FOLLOW_BLOCK_END_in_atom_expr1619 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_61_in_atom_expr1634 = new BitSet(new long[]{0x6100029002001000L});
	public static final BitSet FOLLOW_expressions_in_atom_expr1636 = new BitSet(new long[]{0x4000000000000000L});
	public static final BitSet FOLLOW_62_in_atom_expr1639 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_56_in_quantifier1660 = new BitSet(new long[]{0x0000000000200010L});
	public static final BitSet FOLLOW_ALL_in_quantifier1664 = new BitSet(new long[]{0x0000000002000000L});
	public static final BitSet FOLLOW_EX_in_quantifier1669 = new BitSet(new long[]{0x0000000002000000L});
	public static final BitSet FOLLOW_ID_in_quantifier1673 = new BitSet(new long[]{0x0800000000000000L});
	public static final BitSet FOLLOW_59_in_quantifier1675 = new BitSet(new long[]{0x0000800010000080L});
	public static final BitSet FOLLOW_type_in_quantifier1678 = new BitSet(new long[]{0x0000000000020000L});
	public static final BitSet FOLLOW_DOUBLECOLON_in_quantifier1680 = new BitSet(new long[]{0x2100029002001000L});
	public static final BitSet FOLLOW_expression_in_quantifier1683 = new BitSet(new long[]{0x0200000000000000L});
	public static final BitSet FOLLOW_57_in_quantifier1685 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_ID_in_synpred1_Dafny1033 = new BitSet(new long[]{0x0000000000000400L});
	public static final BitSet FOLLOW_ASSIGN_in_synpred1_Dafny1035 = new BitSet(new long[]{0x0000000000004000L});
	public static final BitSet FOLLOW_CALL_in_synpred1_Dafny1037 = new BitSet(new long[]{0x0000000000000002L});
}
