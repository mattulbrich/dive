// $ANTLR 3.5.1 src/edu/kit/iti/algover/parser/Dafny.g 2016-06-15 09:52:57

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
		"BLOCK_BEGIN", "BLOCK_END", "CALL", "CLASS", "DECREASES", "DOT", "DOUBLECOLON", 
		"ELSE", "ENSURES", "EQ", "EX", "FIELD_ACCESS", "FUNCTION", "FUNC_CALL", 
		"GE", "GT", "HAVOC", "ID", "IF", "IMPLIES", "INT", "INTERSECT", "INVARIANT", 
		"LABEL", "LE", "LEMMA", "LENGTH", "LISTEX", "LIT", "LT", "METHOD", "MINUS", 
		"MODIFIES", "MULTILINE_COMMENT", "NEQ", "NOT", "NULL", "OBJ_FUNC_CALL", 
		"OR", "PLUS", "REQUIRES", "RESULTS", "RETURNS", "SET", "SETEX", "SINGLELINE_COMMENT", 
		"THEN", "THIS", "TIMES", "UNION", "VAR", "WHILE", "WS", "'('", "')'", 
		"','", "':'", "';'", "'['", "']'"
	};
	public static final int EOF=-1;
	public static final int T__67=67;
	public static final int T__68=68;
	public static final int T__69=69;
	public static final int T__70=70;
	public static final int T__71=71;
	public static final int T__72=72;
	public static final int T__73=73;
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
	public static final int CLASS=17;
	public static final int DECREASES=18;
	public static final int DOT=19;
	public static final int DOUBLECOLON=20;
	public static final int ELSE=21;
	public static final int ENSURES=22;
	public static final int EQ=23;
	public static final int EX=24;
	public static final int FIELD_ACCESS=25;
	public static final int FUNCTION=26;
	public static final int FUNC_CALL=27;
	public static final int GE=28;
	public static final int GT=29;
	public static final int HAVOC=30;
	public static final int ID=31;
	public static final int IF=32;
	public static final int IMPLIES=33;
	public static final int INT=34;
	public static final int INTERSECT=35;
	public static final int INVARIANT=36;
	public static final int LABEL=37;
	public static final int LE=38;
	public static final int LEMMA=39;
	public static final int LENGTH=40;
	public static final int LISTEX=41;
	public static final int LIT=42;
	public static final int LT=43;
	public static final int METHOD=44;
	public static final int MINUS=45;
	public static final int MODIFIES=46;
	public static final int MULTILINE_COMMENT=47;
	public static final int NEQ=48;
	public static final int NOT=49;
	public static final int NULL=50;
	public static final int OBJ_FUNC_CALL=51;
	public static final int OR=52;
	public static final int PLUS=53;
	public static final int REQUIRES=54;
	public static final int RESULTS=55;
	public static final int RETURNS=56;
	public static final int SET=57;
	public static final int SETEX=58;
	public static final int SINGLELINE_COMMENT=59;
	public static final int THEN=60;
	public static final int THIS=61;
	public static final int TIMES=62;
	public static final int UNION=63;
	public static final int VAR=64;
	public static final int WHILE=65;
	public static final int WS=66;

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
	@Override public String getGrammarFileName() { return "src/edu/kit/iti/algover/parser/Dafny.g"; }


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
	// src/edu/kit/iti/algover/parser/Dafny.g:118:1: label : 'label' ^ ID ':' !;
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
			// src/edu/kit/iti/algover/parser/Dafny.g:118:6: ( 'label' ^ ID ':' !)
			// src/edu/kit/iti/algover/parser/Dafny.g:119:3: 'label' ^ ID ':' !
			{
			root_0 = (DafnyTree)adaptor.nil();


			string_literal1=(Token)match(input,LABEL,FOLLOW_LABEL_in_label590); if (state.failed) return retval;
			if ( state.backtracking==0 ) {
			string_literal1_tree = (DafnyTree)adaptor.create(string_literal1);
			root_0 = (DafnyTree)adaptor.becomeRoot(string_literal1_tree, root_0);
			}

			ID2=(Token)match(input,ID,FOLLOW_ID_in_label593); if (state.failed) return retval;
			if ( state.backtracking==0 ) {
			ID2_tree = (DafnyTree)adaptor.create(ID2);
			adaptor.addChild(root_0, ID2_tree);
			}

			char_literal3=(Token)match(input,70,FOLLOW_70_in_label595); if (state.failed) return retval;
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
	// src/edu/kit/iti/algover/parser/Dafny.g:122:1: program : ( method | function | clazz )+ ;
	public final DafnyParser.program_return program() throws RecognitionException {
		DafnyParser.program_return retval = new DafnyParser.program_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		ParserRuleReturnScope method4 =null;
		ParserRuleReturnScope function5 =null;
		ParserRuleReturnScope clazz6 =null;


		try {
			// src/edu/kit/iti/algover/parser/Dafny.g:122:8: ( ( method | function | clazz )+ )
			// src/edu/kit/iti/algover/parser/Dafny.g:123:3: ( method | function | clazz )+
			{
			root_0 = (DafnyTree)adaptor.nil();


			// src/edu/kit/iti/algover/parser/Dafny.g:123:3: ( method | function | clazz )+
			int cnt1=0;
			loop1:
			while (true) {
				int alt1=4;
				switch ( input.LA(1) ) {
				case LEMMA:
				case METHOD:
					{
					alt1=1;
					}
					break;
				case FUNCTION:
					{
					alt1=2;
					}
					break;
				case CLASS:
					{
					alt1=3;
					}
					break;
				}
				switch (alt1) {
				case 1 :
					// src/edu/kit/iti/algover/parser/Dafny.g:123:4: method
					{
					pushFollow(FOLLOW_method_in_program609);
					method4=method();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, method4.getTree());

					}
					break;
				case 2 :
					// src/edu/kit/iti/algover/parser/Dafny.g:123:13: function
					{
					pushFollow(FOLLOW_function_in_program613);
					function5=function();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, function5.getTree());

					}
					break;
				case 3 :
					// src/edu/kit/iti/algover/parser/Dafny.g:123:24: clazz
					{
					pushFollow(FOLLOW_clazz_in_program617);
					clazz6=clazz();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, clazz6.getTree());

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


	public static class clazz_return extends ParserRuleReturnScope {
		DafnyTree tree;
		@Override
		public DafnyTree getTree() { return tree; }
	};


	// $ANTLR start "clazz"
	// src/edu/kit/iti/algover/parser/Dafny.g:127:1: clazz : CLASS ^ ID '{' ( method | function | field )+ '}' ;
	public final DafnyParser.clazz_return clazz() throws RecognitionException {
		DafnyParser.clazz_return retval = new DafnyParser.clazz_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		Token CLASS7=null;
		Token ID8=null;
		Token char_literal9=null;
		Token char_literal13=null;
		ParserRuleReturnScope method10 =null;
		ParserRuleReturnScope function11 =null;
		ParserRuleReturnScope field12 =null;

		DafnyTree CLASS7_tree=null;
		DafnyTree ID8_tree=null;
		DafnyTree char_literal9_tree=null;
		DafnyTree char_literal13_tree=null;

		try {
			// src/edu/kit/iti/algover/parser/Dafny.g:127:6: ( CLASS ^ ID '{' ( method | function | field )+ '}' )
			// src/edu/kit/iti/algover/parser/Dafny.g:128:3: CLASS ^ ID '{' ( method | function | field )+ '}'
			{
			root_0 = (DafnyTree)adaptor.nil();


			CLASS7=(Token)match(input,CLASS,FOLLOW_CLASS_in_clazz632); if (state.failed) return retval;
			if ( state.backtracking==0 ) {
			CLASS7_tree = (DafnyTree)adaptor.create(CLASS7);
			root_0 = (DafnyTree)adaptor.becomeRoot(CLASS7_tree, root_0);
			}

			ID8=(Token)match(input,ID,FOLLOW_ID_in_clazz635); if (state.failed) return retval;
			if ( state.backtracking==0 ) {
			ID8_tree = (DafnyTree)adaptor.create(ID8);
			adaptor.addChild(root_0, ID8_tree);
			}

			char_literal9=(Token)match(input,BLOCK_BEGIN,FOLLOW_BLOCK_BEGIN_in_clazz637); if (state.failed) return retval;
			if ( state.backtracking==0 ) {
			char_literal9_tree = (DafnyTree)adaptor.create(char_literal9);
			adaptor.addChild(root_0, char_literal9_tree);
			}

			// src/edu/kit/iti/algover/parser/Dafny.g:129:5: ( method | function | field )+
			int cnt2=0;
			loop2:
			while (true) {
				int alt2=4;
				switch ( input.LA(1) ) {
				case LEMMA:
				case METHOD:
					{
					alt2=1;
					}
					break;
				case FUNCTION:
					{
					alt2=2;
					}
					break;
				case VAR:
					{
					alt2=3;
					}
					break;
				}
				switch (alt2) {
				case 1 :
					// src/edu/kit/iti/algover/parser/Dafny.g:129:6: method
					{
					pushFollow(FOLLOW_method_in_clazz644);
					method10=method();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, method10.getTree());

					}
					break;
				case 2 :
					// src/edu/kit/iti/algover/parser/Dafny.g:129:15: function
					{
					pushFollow(FOLLOW_function_in_clazz648);
					function11=function();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, function11.getTree());

					}
					break;
				case 3 :
					// src/edu/kit/iti/algover/parser/Dafny.g:129:26: field
					{
					pushFollow(FOLLOW_field_in_clazz652);
					field12=field();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, field12.getTree());

					}
					break;

				default :
					if ( cnt2 >= 1 ) break loop2;
					if (state.backtracking>0) {state.failed=true; return retval;}
					EarlyExitException eee = new EarlyExitException(2, input);
					throw eee;
				}
				cnt2++;
			}

			char_literal13=(Token)match(input,BLOCK_END,FOLLOW_BLOCK_END_in_clazz658); if (state.failed) return retval;
			if ( state.backtracking==0 ) {
			char_literal13_tree = (DafnyTree)adaptor.create(char_literal13);
			adaptor.addChild(root_0, char_literal13_tree);
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
	// $ANTLR end "clazz"


	public static class method_return extends ParserRuleReturnScope {
		DafnyTree tree;
		@Override
		public DafnyTree getTree() { return tree; }
	};


	// $ANTLR start "method"
	// src/edu/kit/iti/algover/parser/Dafny.g:133:1: method : tok= ( 'method' | 'lemma' ) ID '(' ( vars )? ')' ( returns_ )? ( requires )* ( ensures )* ( decreases )? '{' ( statements )? '}' -> ^( METHOD[tok] ID ^( ARGS ( vars )? ) ( returns_ )? ( requires )* ( ensures )* ( decreases )? ^( BLOCK ( statements )? ) ) ;
	public final DafnyParser.method_return method() throws RecognitionException {
		DafnyParser.method_return retval = new DafnyParser.method_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		Token tok=null;
		Token ID14=null;
		Token char_literal15=null;
		Token char_literal17=null;
		Token char_literal22=null;
		Token char_literal24=null;
		ParserRuleReturnScope vars16 =null;
		ParserRuleReturnScope returns_18 =null;
		ParserRuleReturnScope requires19 =null;
		ParserRuleReturnScope ensures20 =null;
		ParserRuleReturnScope decreases21 =null;
		ParserRuleReturnScope statements23 =null;

		DafnyTree tok_tree=null;
		DafnyTree ID14_tree=null;
		DafnyTree char_literal15_tree=null;
		DafnyTree char_literal17_tree=null;
		DafnyTree char_literal22_tree=null;
		DafnyTree char_literal24_tree=null;
		RewriteRuleTokenStream stream_67=new RewriteRuleTokenStream(adaptor,"token 67");
		RewriteRuleTokenStream stream_68=new RewriteRuleTokenStream(adaptor,"token 68");
		RewriteRuleTokenStream stream_BLOCK_END=new RewriteRuleTokenStream(adaptor,"token BLOCK_END");
		RewriteRuleTokenStream stream_BLOCK_BEGIN=new RewriteRuleTokenStream(adaptor,"token BLOCK_BEGIN");
		RewriteRuleTokenStream stream_LEMMA=new RewriteRuleTokenStream(adaptor,"token LEMMA");
		RewriteRuleTokenStream stream_METHOD=new RewriteRuleTokenStream(adaptor,"token METHOD");
		RewriteRuleTokenStream stream_ID=new RewriteRuleTokenStream(adaptor,"token ID");
		RewriteRuleSubtreeStream stream_ensures=new RewriteRuleSubtreeStream(adaptor,"rule ensures");
		RewriteRuleSubtreeStream stream_decreases=new RewriteRuleSubtreeStream(adaptor,"rule decreases");
		RewriteRuleSubtreeStream stream_statements=new RewriteRuleSubtreeStream(adaptor,"rule statements");
		RewriteRuleSubtreeStream stream_vars=new RewriteRuleSubtreeStream(adaptor,"rule vars");
		RewriteRuleSubtreeStream stream_returns_=new RewriteRuleSubtreeStream(adaptor,"rule returns_");
		RewriteRuleSubtreeStream stream_requires=new RewriteRuleSubtreeStream(adaptor,"rule requires");

		try {
			// src/edu/kit/iti/algover/parser/Dafny.g:133:7: (tok= ( 'method' | 'lemma' ) ID '(' ( vars )? ')' ( returns_ )? ( requires )* ( ensures )* ( decreases )? '{' ( statements )? '}' -> ^( METHOD[tok] ID ^( ARGS ( vars )? ) ( returns_ )? ( requires )* ( ensures )* ( decreases )? ^( BLOCK ( statements )? ) ) )
			// src/edu/kit/iti/algover/parser/Dafny.g:134:3: tok= ( 'method' | 'lemma' ) ID '(' ( vars )? ')' ( returns_ )? ( requires )* ( ensures )* ( decreases )? '{' ( statements )? '}'
			{
			// src/edu/kit/iti/algover/parser/Dafny.g:134:9: ( 'method' | 'lemma' )
			int alt3=2;
			int LA3_0 = input.LA(1);
			if ( (LA3_0==METHOD) ) {
				alt3=1;
			}
			else if ( (LA3_0==LEMMA) ) {
				alt3=2;
			}

			else {
				if (state.backtracking>0) {state.failed=true; return retval;}
				NoViableAltException nvae =
					new NoViableAltException("", 3, 0, input);
				throw nvae;
			}

			switch (alt3) {
				case 1 :
					// src/edu/kit/iti/algover/parser/Dafny.g:134:10: 'method'
					{
					tok=(Token)match(input,METHOD,FOLLOW_METHOD_in_method676); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_METHOD.add(tok);

					}
					break;
				case 2 :
					// src/edu/kit/iti/algover/parser/Dafny.g:134:21: 'lemma'
					{
					tok=(Token)match(input,LEMMA,FOLLOW_LEMMA_in_method680); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_LEMMA.add(tok);

					}
					break;

			}

			ID14=(Token)match(input,ID,FOLLOW_ID_in_method685); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_ID.add(ID14);

			char_literal15=(Token)match(input,67,FOLLOW_67_in_method687); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_67.add(char_literal15);

			// src/edu/kit/iti/algover/parser/Dafny.g:135:10: ( vars )?
			int alt4=2;
			int LA4_0 = input.LA(1);
			if ( (LA4_0==ID) ) {
				alt4=1;
			}
			switch (alt4) {
				case 1 :
					// src/edu/kit/iti/algover/parser/Dafny.g:135:10: vars
					{
					pushFollow(FOLLOW_vars_in_method689);
					vars16=vars();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_vars.add(vars16.getTree());
					}
					break;

			}

			char_literal17=(Token)match(input,68,FOLLOW_68_in_method692); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_68.add(char_literal17);

			// src/edu/kit/iti/algover/parser/Dafny.g:136:3: ( returns_ )?
			int alt5=2;
			int LA5_0 = input.LA(1);
			if ( (LA5_0==RETURNS) ) {
				alt5=1;
			}
			switch (alt5) {
				case 1 :
					// src/edu/kit/iti/algover/parser/Dafny.g:136:5: returns_
					{
					pushFollow(FOLLOW_returns__in_method698);
					returns_18=returns_();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_returns_.add(returns_18.getTree());
					}
					break;

			}

			// src/edu/kit/iti/algover/parser/Dafny.g:137:3: ( requires )*
			loop6:
			while (true) {
				int alt6=2;
				int LA6_0 = input.LA(1);
				if ( (LA6_0==REQUIRES) ) {
					alt6=1;
				}

				switch (alt6) {
				case 1 :
					// src/edu/kit/iti/algover/parser/Dafny.g:137:5: requires
					{
					pushFollow(FOLLOW_requires_in_method707);
					requires19=requires();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_requires.add(requires19.getTree());
					}
					break;

				default :
					break loop6;
				}
			}

			// src/edu/kit/iti/algover/parser/Dafny.g:138:3: ( ensures )*
			loop7:
			while (true) {
				int alt7=2;
				int LA7_0 = input.LA(1);
				if ( (LA7_0==ENSURES) ) {
					alt7=1;
				}

				switch (alt7) {
				case 1 :
					// src/edu/kit/iti/algover/parser/Dafny.g:138:5: ensures
					{
					pushFollow(FOLLOW_ensures_in_method716);
					ensures20=ensures();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_ensures.add(ensures20.getTree());
					}
					break;

				default :
					break loop7;
				}
			}

			// src/edu/kit/iti/algover/parser/Dafny.g:139:3: ( decreases )?
			int alt8=2;
			int LA8_0 = input.LA(1);
			if ( (LA8_0==DECREASES) ) {
				alt8=1;
			}
			switch (alt8) {
				case 1 :
					// src/edu/kit/iti/algover/parser/Dafny.g:139:5: decreases
					{
					pushFollow(FOLLOW_decreases_in_method725);
					decreases21=decreases();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_decreases.add(decreases21.getTree());
					}
					break;

			}

			char_literal22=(Token)match(input,BLOCK_BEGIN,FOLLOW_BLOCK_BEGIN_in_method732); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_BLOCK_BEGIN.add(char_literal22);

			// src/edu/kit/iti/algover/parser/Dafny.g:140:7: ( statements )?
			int alt9=2;
			int LA9_0 = input.LA(1);
			if ( (LA9_0==ASSERT||LA9_0==ASSUME||(LA9_0 >= ID && LA9_0 <= IF)||LA9_0==LABEL||(LA9_0 >= VAR && LA9_0 <= WHILE)) ) {
				alt9=1;
			}
			switch (alt9) {
				case 1 :
					// src/edu/kit/iti/algover/parser/Dafny.g:140:7: statements
					{
					pushFollow(FOLLOW_statements_in_method734);
					statements23=statements();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_statements.add(statements23.getTree());
					}
					break;

			}

			char_literal24=(Token)match(input,BLOCK_END,FOLLOW_BLOCK_END_in_method737); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_BLOCK_END.add(char_literal24);

			// AST REWRITE
			// elements: vars, ID, requires, statements, returns_, decreases, ensures
			// token labels: 
			// rule labels: retval
			// token list labels: 
			// rule list labels: 
			// wildcard labels: 
			if ( state.backtracking==0 ) {
			retval.tree = root_0;
			RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

			root_0 = (DafnyTree)adaptor.nil();
			// 141:3: -> ^( METHOD[tok] ID ^( ARGS ( vars )? ) ( returns_ )? ( requires )* ( ensures )* ( decreases )? ^( BLOCK ( statements )? ) )
			{
				// src/edu/kit/iti/algover/parser/Dafny.g:142:5: ^( METHOD[tok] ID ^( ARGS ( vars )? ) ( returns_ )? ( requires )* ( ensures )* ( decreases )? ^( BLOCK ( statements )? ) )
				{
				DafnyTree root_1 = (DafnyTree)adaptor.nil();
				root_1 = (DafnyTree)adaptor.becomeRoot((DafnyTree)adaptor.create(METHOD, tok), root_1);
				adaptor.addChild(root_1, stream_ID.nextNode());
				// src/edu/kit/iti/algover/parser/Dafny.g:142:22: ^( ARGS ( vars )? )
				{
				DafnyTree root_2 = (DafnyTree)adaptor.nil();
				root_2 = (DafnyTree)adaptor.becomeRoot((DafnyTree)adaptor.create(ARGS, "ARGS"), root_2);
				// src/edu/kit/iti/algover/parser/Dafny.g:142:29: ( vars )?
				if ( stream_vars.hasNext() ) {
					adaptor.addChild(root_2, stream_vars.nextTree());
				}
				stream_vars.reset();

				adaptor.addChild(root_1, root_2);
				}

				// src/edu/kit/iti/algover/parser/Dafny.g:142:36: ( returns_ )?
				if ( stream_returns_.hasNext() ) {
					adaptor.addChild(root_1, stream_returns_.nextTree());
				}
				stream_returns_.reset();

				// src/edu/kit/iti/algover/parser/Dafny.g:142:46: ( requires )*
				while ( stream_requires.hasNext() ) {
					adaptor.addChild(root_1, stream_requires.nextTree());
				}
				stream_requires.reset();

				// src/edu/kit/iti/algover/parser/Dafny.g:142:56: ( ensures )*
				while ( stream_ensures.hasNext() ) {
					adaptor.addChild(root_1, stream_ensures.nextTree());
				}
				stream_ensures.reset();

				// src/edu/kit/iti/algover/parser/Dafny.g:143:9: ( decreases )?
				if ( stream_decreases.hasNext() ) {
					adaptor.addChild(root_1, stream_decreases.nextTree());
				}
				stream_decreases.reset();

				// src/edu/kit/iti/algover/parser/Dafny.g:143:20: ^( BLOCK ( statements )? )
				{
				DafnyTree root_2 = (DafnyTree)adaptor.nil();
				root_2 = (DafnyTree)adaptor.becomeRoot((DafnyTree)adaptor.create(BLOCK, "BLOCK"), root_2);
				// src/edu/kit/iti/algover/parser/Dafny.g:143:28: ( statements )?
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
	// src/edu/kit/iti/algover/parser/Dafny.g:146:1: function : 'function' ^ ID '(' ! ( vars )? ')' ! ':' ! type '{' ! expression '}' !;
	public final DafnyParser.function_return function() throws RecognitionException {
		DafnyParser.function_return retval = new DafnyParser.function_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		Token string_literal25=null;
		Token ID26=null;
		Token char_literal27=null;
		Token char_literal29=null;
		Token char_literal30=null;
		Token char_literal32=null;
		Token char_literal34=null;
		ParserRuleReturnScope vars28 =null;
		ParserRuleReturnScope type31 =null;
		ParserRuleReturnScope expression33 =null;

		DafnyTree string_literal25_tree=null;
		DafnyTree ID26_tree=null;
		DafnyTree char_literal27_tree=null;
		DafnyTree char_literal29_tree=null;
		DafnyTree char_literal30_tree=null;
		DafnyTree char_literal32_tree=null;
		DafnyTree char_literal34_tree=null;

		try {
			// src/edu/kit/iti/algover/parser/Dafny.g:146:9: ( 'function' ^ ID '(' ! ( vars )? ')' ! ':' ! type '{' ! expression '}' !)
			// src/edu/kit/iti/algover/parser/Dafny.g:147:3: 'function' ^ ID '(' ! ( vars )? ')' ! ':' ! type '{' ! expression '}' !
			{
			root_0 = (DafnyTree)adaptor.nil();


			string_literal25=(Token)match(input,FUNCTION,FOLLOW_FUNCTION_in_function799); if (state.failed) return retval;
			if ( state.backtracking==0 ) {
			string_literal25_tree = (DafnyTree)adaptor.create(string_literal25);
			root_0 = (DafnyTree)adaptor.becomeRoot(string_literal25_tree, root_0);
			}

			ID26=(Token)match(input,ID,FOLLOW_ID_in_function804); if (state.failed) return retval;
			if ( state.backtracking==0 ) {
			ID26_tree = (DafnyTree)adaptor.create(ID26);
			adaptor.addChild(root_0, ID26_tree);
			}

			char_literal27=(Token)match(input,67,FOLLOW_67_in_function806); if (state.failed) return retval;
			// src/edu/kit/iti/algover/parser/Dafny.g:148:11: ( vars )?
			int alt10=2;
			int LA10_0 = input.LA(1);
			if ( (LA10_0==ID) ) {
				alt10=1;
			}
			switch (alt10) {
				case 1 :
					// src/edu/kit/iti/algover/parser/Dafny.g:148:11: vars
					{
					pushFollow(FOLLOW_vars_in_function809);
					vars28=vars();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, vars28.getTree());

					}
					break;

			}

			char_literal29=(Token)match(input,68,FOLLOW_68_in_function812); if (state.failed) return retval;
			char_literal30=(Token)match(input,70,FOLLOW_70_in_function815); if (state.failed) return retval;
			pushFollow(FOLLOW_type_in_function818);
			type31=type();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, type31.getTree());

			char_literal32=(Token)match(input,BLOCK_BEGIN,FOLLOW_BLOCK_BEGIN_in_function822); if (state.failed) return retval;
			pushFollow(FOLLOW_expression_in_function825);
			expression33=expression();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, expression33.getTree());

			char_literal34=(Token)match(input,BLOCK_END,FOLLOW_BLOCK_END_in_function827); if (state.failed) return retval;
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


	public static class field_return extends ParserRuleReturnScope {
		DafnyTree tree;
		@Override
		public DafnyTree getTree() { return tree; }
	};


	// $ANTLR start "field"
	// src/edu/kit/iti/algover/parser/Dafny.g:152:1: field : 'var' ID ':' type ';' ;
	public final DafnyParser.field_return field() throws RecognitionException {
		DafnyParser.field_return retval = new DafnyParser.field_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		Token string_literal35=null;
		Token ID36=null;
		Token char_literal37=null;
		Token char_literal39=null;
		ParserRuleReturnScope type38 =null;

		DafnyTree string_literal35_tree=null;
		DafnyTree ID36_tree=null;
		DafnyTree char_literal37_tree=null;
		DafnyTree char_literal39_tree=null;

		try {
			// src/edu/kit/iti/algover/parser/Dafny.g:152:6: ( 'var' ID ':' type ';' )
			// src/edu/kit/iti/algover/parser/Dafny.g:153:3: 'var' ID ':' type ';'
			{
			root_0 = (DafnyTree)adaptor.nil();


			string_literal35=(Token)match(input,VAR,FOLLOW_VAR_in_field840); if (state.failed) return retval;
			if ( state.backtracking==0 ) {
			string_literal35_tree = (DafnyTree)adaptor.create(string_literal35);
			adaptor.addChild(root_0, string_literal35_tree);
			}

			ID36=(Token)match(input,ID,FOLLOW_ID_in_field842); if (state.failed) return retval;
			if ( state.backtracking==0 ) {
			ID36_tree = (DafnyTree)adaptor.create(ID36);
			adaptor.addChild(root_0, ID36_tree);
			}

			char_literal37=(Token)match(input,70,FOLLOW_70_in_field844); if (state.failed) return retval;
			if ( state.backtracking==0 ) {
			char_literal37_tree = (DafnyTree)adaptor.create(char_literal37);
			adaptor.addChild(root_0, char_literal37_tree);
			}

			pushFollow(FOLLOW_type_in_field846);
			type38=type();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, type38.getTree());

			char_literal39=(Token)match(input,71,FOLLOW_71_in_field848); if (state.failed) return retval;
			if ( state.backtracking==0 ) {
			char_literal39_tree = (DafnyTree)adaptor.create(char_literal39);
			adaptor.addChild(root_0, char_literal39_tree);
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
	// $ANTLR end "field"


	public static class vars_return extends ParserRuleReturnScope {
		DafnyTree tree;
		@Override
		public DafnyTree getTree() { return tree; }
	};


	// $ANTLR start "vars"
	// src/edu/kit/iti/algover/parser/Dafny.g:156:1: vars : var ( ',' ! var )* ;
	public final DafnyParser.vars_return vars() throws RecognitionException {
		DafnyParser.vars_return retval = new DafnyParser.vars_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		Token char_literal41=null;
		ParserRuleReturnScope var40 =null;
		ParserRuleReturnScope var42 =null;

		DafnyTree char_literal41_tree=null;

		try {
			// src/edu/kit/iti/algover/parser/Dafny.g:156:5: ( var ( ',' ! var )* )
			// src/edu/kit/iti/algover/parser/Dafny.g:157:3: var ( ',' ! var )*
			{
			root_0 = (DafnyTree)adaptor.nil();


			pushFollow(FOLLOW_var_in_vars860);
			var40=var();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, var40.getTree());

			// src/edu/kit/iti/algover/parser/Dafny.g:158:3: ( ',' ! var )*
			loop11:
			while (true) {
				int alt11=2;
				int LA11_0 = input.LA(1);
				if ( (LA11_0==69) ) {
					alt11=1;
				}

				switch (alt11) {
				case 1 :
					// src/edu/kit/iti/algover/parser/Dafny.g:158:5: ',' ! var
					{
					char_literal41=(Token)match(input,69,FOLLOW_69_in_vars866); if (state.failed) return retval;
					pushFollow(FOLLOW_var_in_vars869);
					var42=var();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, var42.getTree());

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
	// src/edu/kit/iti/algover/parser/Dafny.g:161:1: var : ID ':' type -> ^( VAR ID type ) ;
	public final DafnyParser.var_return var() throws RecognitionException {
		DafnyParser.var_return retval = new DafnyParser.var_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		Token ID43=null;
		Token char_literal44=null;
		ParserRuleReturnScope type45 =null;

		DafnyTree ID43_tree=null;
		DafnyTree char_literal44_tree=null;
		RewriteRuleTokenStream stream_70=new RewriteRuleTokenStream(adaptor,"token 70");
		RewriteRuleTokenStream stream_ID=new RewriteRuleTokenStream(adaptor,"token ID");
		RewriteRuleSubtreeStream stream_type=new RewriteRuleSubtreeStream(adaptor,"rule type");

		try {
			// src/edu/kit/iti/algover/parser/Dafny.g:161:4: ( ID ':' type -> ^( VAR ID type ) )
			// src/edu/kit/iti/algover/parser/Dafny.g:162:3: ID ':' type
			{
			ID43=(Token)match(input,ID,FOLLOW_ID_in_var884); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_ID.add(ID43);

			char_literal44=(Token)match(input,70,FOLLOW_70_in_var886); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_70.add(char_literal44);

			pushFollow(FOLLOW_type_in_var888);
			type45=type();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) stream_type.add(type45.getTree());
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
			// 162:15: -> ^( VAR ID type )
			{
				// src/edu/kit/iti/algover/parser/Dafny.g:162:18: ^( VAR ID type )
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
	// src/edu/kit/iti/algover/parser/Dafny.g:165:1: type : ( INT | SET ^ '<' ! INT '>' !| ARRAY ^ '<' ! INT '>' !);
	public final DafnyParser.type_return type() throws RecognitionException {
		DafnyParser.type_return retval = new DafnyParser.type_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		Token INT46=null;
		Token SET47=null;
		Token char_literal48=null;
		Token INT49=null;
		Token char_literal50=null;
		Token ARRAY51=null;
		Token char_literal52=null;
		Token INT53=null;
		Token char_literal54=null;

		DafnyTree INT46_tree=null;
		DafnyTree SET47_tree=null;
		DafnyTree char_literal48_tree=null;
		DafnyTree INT49_tree=null;
		DafnyTree char_literal50_tree=null;
		DafnyTree ARRAY51_tree=null;
		DafnyTree char_literal52_tree=null;
		DafnyTree INT53_tree=null;
		DafnyTree char_literal54_tree=null;

		try {
			// src/edu/kit/iti/algover/parser/Dafny.g:165:5: ( INT | SET ^ '<' ! INT '>' !| ARRAY ^ '<' ! INT '>' !)
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
					// src/edu/kit/iti/algover/parser/Dafny.g:166:5: INT
					{
					root_0 = (DafnyTree)adaptor.nil();


					INT46=(Token)match(input,INT,FOLLOW_INT_in_type912); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					INT46_tree = (DafnyTree)adaptor.create(INT46);
					adaptor.addChild(root_0, INT46_tree);
					}

					}
					break;
				case 2 :
					// src/edu/kit/iti/algover/parser/Dafny.g:166:11: SET ^ '<' ! INT '>' !
					{
					root_0 = (DafnyTree)adaptor.nil();


					SET47=(Token)match(input,SET,FOLLOW_SET_in_type916); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					SET47_tree = (DafnyTree)adaptor.create(SET47);
					root_0 = (DafnyTree)adaptor.becomeRoot(SET47_tree, root_0);
					}

					char_literal48=(Token)match(input,LT,FOLLOW_LT_in_type919); if (state.failed) return retval;
					INT49=(Token)match(input,INT,FOLLOW_INT_in_type922); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					INT49_tree = (DafnyTree)adaptor.create(INT49);
					adaptor.addChild(root_0, INT49_tree);
					}

					char_literal50=(Token)match(input,GT,FOLLOW_GT_in_type924); if (state.failed) return retval;
					}
					break;
				case 3 :
					// src/edu/kit/iti/algover/parser/Dafny.g:167:5: ARRAY ^ '<' ! INT '>' !
					{
					root_0 = (DafnyTree)adaptor.nil();


					ARRAY51=(Token)match(input,ARRAY,FOLLOW_ARRAY_in_type931); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					ARRAY51_tree = (DafnyTree)adaptor.create(ARRAY51);
					root_0 = (DafnyTree)adaptor.becomeRoot(ARRAY51_tree, root_0);
					}

					char_literal52=(Token)match(input,LT,FOLLOW_LT_in_type934); if (state.failed) return retval;
					INT53=(Token)match(input,INT,FOLLOW_INT_in_type937); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					INT53_tree = (DafnyTree)adaptor.create(INT53);
					adaptor.addChild(root_0, INT53_tree);
					}

					char_literal54=(Token)match(input,GT,FOLLOW_GT_in_type939); if (state.failed) return retval;
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
	// src/edu/kit/iti/algover/parser/Dafny.g:170:1: returns_ : RETURNS ^ '(' ! vars ')' !;
	public final DafnyParser.returns__return returns_() throws RecognitionException {
		DafnyParser.returns__return retval = new DafnyParser.returns__return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		Token RETURNS55=null;
		Token char_literal56=null;
		Token char_literal58=null;
		ParserRuleReturnScope vars57 =null;

		DafnyTree RETURNS55_tree=null;
		DafnyTree char_literal56_tree=null;
		DafnyTree char_literal58_tree=null;

		try {
			// src/edu/kit/iti/algover/parser/Dafny.g:170:9: ( RETURNS ^ '(' ! vars ')' !)
			// src/edu/kit/iti/algover/parser/Dafny.g:171:3: RETURNS ^ '(' ! vars ')' !
			{
			root_0 = (DafnyTree)adaptor.nil();


			RETURNS55=(Token)match(input,RETURNS,FOLLOW_RETURNS_in_returns_952); if (state.failed) return retval;
			if ( state.backtracking==0 ) {
			RETURNS55_tree = (DafnyTree)adaptor.create(RETURNS55);
			root_0 = (DafnyTree)adaptor.becomeRoot(RETURNS55_tree, root_0);
			}

			char_literal56=(Token)match(input,67,FOLLOW_67_in_returns_955); if (state.failed) return retval;
			pushFollow(FOLLOW_vars_in_returns_958);
			vars57=vars();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, vars57.getTree());

			char_literal58=(Token)match(input,68,FOLLOW_68_in_returns_960); if (state.failed) return retval;
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
	// src/edu/kit/iti/algover/parser/Dafny.g:174:1: requires : REQUIRES ^ ( label )? expression ;
	public final DafnyParser.requires_return requires() throws RecognitionException {
		DafnyParser.requires_return retval = new DafnyParser.requires_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		Token REQUIRES59=null;
		ParserRuleReturnScope label60 =null;
		ParserRuleReturnScope expression61 =null;

		DafnyTree REQUIRES59_tree=null;

		try {
			// src/edu/kit/iti/algover/parser/Dafny.g:174:9: ( REQUIRES ^ ( label )? expression )
			// src/edu/kit/iti/algover/parser/Dafny.g:175:3: REQUIRES ^ ( label )? expression
			{
			root_0 = (DafnyTree)adaptor.nil();


			REQUIRES59=(Token)match(input,REQUIRES,FOLLOW_REQUIRES_in_requires973); if (state.failed) return retval;
			if ( state.backtracking==0 ) {
			REQUIRES59_tree = (DafnyTree)adaptor.create(REQUIRES59);
			root_0 = (DafnyTree)adaptor.becomeRoot(REQUIRES59_tree, root_0);
			}

			// src/edu/kit/iti/algover/parser/Dafny.g:175:13: ( label )?
			int alt13=2;
			int LA13_0 = input.LA(1);
			if ( (LA13_0==LABEL) ) {
				alt13=1;
			}
			switch (alt13) {
				case 1 :
					// src/edu/kit/iti/algover/parser/Dafny.g:175:13: label
					{
					pushFollow(FOLLOW_label_in_requires976);
					label60=label();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, label60.getTree());

					}
					break;

			}

			pushFollow(FOLLOW_expression_in_requires979);
			expression61=expression();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, expression61.getTree());

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
	// src/edu/kit/iti/algover/parser/Dafny.g:178:1: ensures : ENSURES ^ ( label )? expression ;
	public final DafnyParser.ensures_return ensures() throws RecognitionException {
		DafnyParser.ensures_return retval = new DafnyParser.ensures_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		Token ENSURES62=null;
		ParserRuleReturnScope label63 =null;
		ParserRuleReturnScope expression64 =null;

		DafnyTree ENSURES62_tree=null;

		try {
			// src/edu/kit/iti/algover/parser/Dafny.g:178:8: ( ENSURES ^ ( label )? expression )
			// src/edu/kit/iti/algover/parser/Dafny.g:179:3: ENSURES ^ ( label )? expression
			{
			root_0 = (DafnyTree)adaptor.nil();


			ENSURES62=(Token)match(input,ENSURES,FOLLOW_ENSURES_in_ensures991); if (state.failed) return retval;
			if ( state.backtracking==0 ) {
			ENSURES62_tree = (DafnyTree)adaptor.create(ENSURES62);
			root_0 = (DafnyTree)adaptor.becomeRoot(ENSURES62_tree, root_0);
			}

			// src/edu/kit/iti/algover/parser/Dafny.g:179:12: ( label )?
			int alt14=2;
			int LA14_0 = input.LA(1);
			if ( (LA14_0==LABEL) ) {
				alt14=1;
			}
			switch (alt14) {
				case 1 :
					// src/edu/kit/iti/algover/parser/Dafny.g:179:12: label
					{
					pushFollow(FOLLOW_label_in_ensures994);
					label63=label();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, label63.getTree());

					}
					break;

			}

			pushFollow(FOLLOW_expression_in_ensures997);
			expression64=expression();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, expression64.getTree());

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
	// src/edu/kit/iti/algover/parser/Dafny.g:182:1: decreases : DECREASES ^ expression ;
	public final DafnyParser.decreases_return decreases() throws RecognitionException {
		DafnyParser.decreases_return retval = new DafnyParser.decreases_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		Token DECREASES65=null;
		ParserRuleReturnScope expression66 =null;

		DafnyTree DECREASES65_tree=null;

		try {
			// src/edu/kit/iti/algover/parser/Dafny.g:182:10: ( DECREASES ^ expression )
			// src/edu/kit/iti/algover/parser/Dafny.g:183:3: DECREASES ^ expression
			{
			root_0 = (DafnyTree)adaptor.nil();


			DECREASES65=(Token)match(input,DECREASES,FOLLOW_DECREASES_in_decreases1009); if (state.failed) return retval;
			if ( state.backtracking==0 ) {
			DECREASES65_tree = (DafnyTree)adaptor.create(DECREASES65);
			root_0 = (DafnyTree)adaptor.becomeRoot(DECREASES65_tree, root_0);
			}

			pushFollow(FOLLOW_expression_in_decreases1012);
			expression66=expression();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, expression66.getTree());

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
	// src/edu/kit/iti/algover/parser/Dafny.g:186:1: invariant : INVARIANT ^ ( label )? expression ;
	public final DafnyParser.invariant_return invariant() throws RecognitionException {
		DafnyParser.invariant_return retval = new DafnyParser.invariant_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		Token INVARIANT67=null;
		ParserRuleReturnScope label68 =null;
		ParserRuleReturnScope expression69 =null;

		DafnyTree INVARIANT67_tree=null;

		try {
			// src/edu/kit/iti/algover/parser/Dafny.g:186:10: ( INVARIANT ^ ( label )? expression )
			// src/edu/kit/iti/algover/parser/Dafny.g:187:3: INVARIANT ^ ( label )? expression
			{
			root_0 = (DafnyTree)adaptor.nil();


			INVARIANT67=(Token)match(input,INVARIANT,FOLLOW_INVARIANT_in_invariant1024); if (state.failed) return retval;
			if ( state.backtracking==0 ) {
			INVARIANT67_tree = (DafnyTree)adaptor.create(INVARIANT67);
			root_0 = (DafnyTree)adaptor.becomeRoot(INVARIANT67_tree, root_0);
			}

			// src/edu/kit/iti/algover/parser/Dafny.g:187:14: ( label )?
			int alt15=2;
			int LA15_0 = input.LA(1);
			if ( (LA15_0==LABEL) ) {
				alt15=1;
			}
			switch (alt15) {
				case 1 :
					// src/edu/kit/iti/algover/parser/Dafny.g:187:14: label
					{
					pushFollow(FOLLOW_label_in_invariant1027);
					label68=label();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, label68.getTree());

					}
					break;

			}

			pushFollow(FOLLOW_expression_in_invariant1030);
			expression69=expression();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, expression69.getTree());

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


	public static class modifies_return extends ParserRuleReturnScope {
		DafnyTree tree;
		@Override
		public DafnyTree getTree() { return tree; }
	};


	// $ANTLR start "modifies"
	// src/edu/kit/iti/algover/parser/Dafny.g:190:1: modifies : MODIFIES ^ expressions ;
	public final DafnyParser.modifies_return modifies() throws RecognitionException {
		DafnyParser.modifies_return retval = new DafnyParser.modifies_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		Token MODIFIES70=null;
		ParserRuleReturnScope expressions71 =null;

		DafnyTree MODIFIES70_tree=null;

		try {
			// src/edu/kit/iti/algover/parser/Dafny.g:190:9: ( MODIFIES ^ expressions )
			// src/edu/kit/iti/algover/parser/Dafny.g:191:3: MODIFIES ^ expressions
			{
			root_0 = (DafnyTree)adaptor.nil();


			MODIFIES70=(Token)match(input,MODIFIES,FOLLOW_MODIFIES_in_modifies1042); if (state.failed) return retval;
			if ( state.backtracking==0 ) {
			MODIFIES70_tree = (DafnyTree)adaptor.create(MODIFIES70);
			root_0 = (DafnyTree)adaptor.becomeRoot(MODIFIES70_tree, root_0);
			}

			pushFollow(FOLLOW_expressions_in_modifies1045);
			expressions71=expressions();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, expressions71.getTree());

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
	// $ANTLR end "modifies"


	public static class block_return extends ParserRuleReturnScope {
		DafnyTree tree;
		@Override
		public DafnyTree getTree() { return tree; }
	};


	// $ANTLR start "block"
	// src/edu/kit/iti/algover/parser/Dafny.g:194:1: block : '{' ( statements )? '}' -> ^( BLOCK ( statements )? ) ;
	public final DafnyParser.block_return block() throws RecognitionException {
		DafnyParser.block_return retval = new DafnyParser.block_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		Token char_literal72=null;
		Token char_literal74=null;
		ParserRuleReturnScope statements73 =null;

		DafnyTree char_literal72_tree=null;
		DafnyTree char_literal74_tree=null;
		RewriteRuleTokenStream stream_BLOCK_END=new RewriteRuleTokenStream(adaptor,"token BLOCK_END");
		RewriteRuleTokenStream stream_BLOCK_BEGIN=new RewriteRuleTokenStream(adaptor,"token BLOCK_BEGIN");
		RewriteRuleSubtreeStream stream_statements=new RewriteRuleSubtreeStream(adaptor,"rule statements");

		try {
			// src/edu/kit/iti/algover/parser/Dafny.g:194:6: ( '{' ( statements )? '}' -> ^( BLOCK ( statements )? ) )
			// src/edu/kit/iti/algover/parser/Dafny.g:195:3: '{' ( statements )? '}'
			{
			char_literal72=(Token)match(input,BLOCK_BEGIN,FOLLOW_BLOCK_BEGIN_in_block1057); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_BLOCK_BEGIN.add(char_literal72);

			// src/edu/kit/iti/algover/parser/Dafny.g:195:7: ( statements )?
			int alt16=2;
			int LA16_0 = input.LA(1);
			if ( (LA16_0==ASSERT||LA16_0==ASSUME||(LA16_0 >= ID && LA16_0 <= IF)||LA16_0==LABEL||(LA16_0 >= VAR && LA16_0 <= WHILE)) ) {
				alt16=1;
			}
			switch (alt16) {
				case 1 :
					// src/edu/kit/iti/algover/parser/Dafny.g:195:7: statements
					{
					pushFollow(FOLLOW_statements_in_block1059);
					statements73=statements();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_statements.add(statements73.getTree());
					}
					break;

			}

			char_literal74=(Token)match(input,BLOCK_END,FOLLOW_BLOCK_END_in_block1062); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_BLOCK_END.add(char_literal74);

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
			// 195:23: -> ^( BLOCK ( statements )? )
			{
				// src/edu/kit/iti/algover/parser/Dafny.g:195:26: ^( BLOCK ( statements )? )
				{
				DafnyTree root_1 = (DafnyTree)adaptor.nil();
				root_1 = (DafnyTree)adaptor.becomeRoot((DafnyTree)adaptor.create(BLOCK, "BLOCK"), root_1);
				// src/edu/kit/iti/algover/parser/Dafny.g:195:34: ( statements )?
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
	// src/edu/kit/iti/algover/parser/Dafny.g:198:1: relaxedBlock : ( block | statement -> ^( BLOCK statement ) );
	public final DafnyParser.relaxedBlock_return relaxedBlock() throws RecognitionException {
		DafnyParser.relaxedBlock_return retval = new DafnyParser.relaxedBlock_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		ParserRuleReturnScope block75 =null;
		ParserRuleReturnScope statement76 =null;

		RewriteRuleSubtreeStream stream_statement=new RewriteRuleSubtreeStream(adaptor,"rule statement");

		try {
			// src/edu/kit/iti/algover/parser/Dafny.g:198:13: ( block | statement -> ^( BLOCK statement ) )
			int alt17=2;
			int LA17_0 = input.LA(1);
			if ( (LA17_0==BLOCK_BEGIN) ) {
				alt17=1;
			}
			else if ( (LA17_0==ASSERT||LA17_0==ASSUME||(LA17_0 >= ID && LA17_0 <= IF)||LA17_0==LABEL||(LA17_0 >= VAR && LA17_0 <= WHILE)) ) {
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
					// src/edu/kit/iti/algover/parser/Dafny.g:199:5: block
					{
					root_0 = (DafnyTree)adaptor.nil();


					pushFollow(FOLLOW_block_in_relaxedBlock1085);
					block75=block();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, block75.getTree());

					}
					break;
				case 2 :
					// src/edu/kit/iti/algover/parser/Dafny.g:200:5: statement
					{
					pushFollow(FOLLOW_statement_in_relaxedBlock1091);
					statement76=statement();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_statement.add(statement76.getTree());
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
					// 200:15: -> ^( BLOCK statement )
					{
						// src/edu/kit/iti/algover/parser/Dafny.g:200:18: ^( BLOCK statement )
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
	// src/edu/kit/iti/algover/parser/Dafny.g:203:1: statements : ( statement )+ ;
	public final DafnyParser.statements_return statements() throws RecognitionException {
		DafnyParser.statements_return retval = new DafnyParser.statements_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		ParserRuleReturnScope statement77 =null;


		try {
			// src/edu/kit/iti/algover/parser/Dafny.g:203:11: ( ( statement )+ )
			// src/edu/kit/iti/algover/parser/Dafny.g:204:3: ( statement )+
			{
			root_0 = (DafnyTree)adaptor.nil();


			// src/edu/kit/iti/algover/parser/Dafny.g:204:3: ( statement )+
			int cnt18=0;
			loop18:
			while (true) {
				int alt18=2;
				int LA18_0 = input.LA(1);
				if ( (LA18_0==ASSERT||LA18_0==ASSUME||(LA18_0 >= ID && LA18_0 <= IF)||LA18_0==LABEL||(LA18_0 >= VAR && LA18_0 <= WHILE)) ) {
					alt18=1;
				}

				switch (alt18) {
				case 1 :
					// src/edu/kit/iti/algover/parser/Dafny.g:204:5: statement
					{
					pushFollow(FOLLOW_statement_in_statements1113);
					statement77=statement();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, statement77.getTree());

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
	// src/edu/kit/iti/algover/parser/Dafny.g:207:1: statement : ( VAR ^ ID ':' ! type ( ':=' ! expression )? ';' !| ID ass= ':=' '*' ';' -> ^( HAVOC[$ass] ID ) | ID ':=' ^ expression ';' !| ID '[' i= expression ']' ass= ':=' v= expression ';' -> ^( ARRAY_UPDATE[$ass] ID $i $v) | ( ID ':=' 'call' )=>r= ID ':=' 'call' f= ID '(' ( expressions )? ')' ';' -> ^( 'call' $f ^( RESULTS $r) ^( ARGS ( expressions )? ) ) | ids ':=' 'call' ID '(' ( expressions )? ')' ';' -> ^( 'call' ID ^( RESULTS ids ) ^( ARGS ( expressions )? ) ) | ( label )? 'while' expression ( invariant )+ ( modifies )? decreases relaxedBlock -> ^( 'while' ( label )? expression ( invariant )+ ( modifies )? decreases relaxedBlock ) | ( label )? 'if' ^ expression relaxedBlock ( options {greedy=true; } : 'else' ! relaxedBlock )? | 'assert' ^ ( 'label' ! ID ':' !)? expression ';' !| 'assume' ^ ( 'label' ! ID ':' !)? expression ';' !);
	public final DafnyParser.statement_return statement() throws RecognitionException {
		DafnyParser.statement_return retval = new DafnyParser.statement_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		Token ass=null;
		Token r=null;
		Token f=null;
		Token VAR78=null;
		Token ID79=null;
		Token char_literal80=null;
		Token string_literal82=null;
		Token char_literal84=null;
		Token ID85=null;
		Token char_literal86=null;
		Token char_literal87=null;
		Token ID88=null;
		Token string_literal89=null;
		Token char_literal91=null;
		Token ID92=null;
		Token char_literal93=null;
		Token char_literal94=null;
		Token char_literal95=null;
		Token string_literal96=null;
		Token string_literal97=null;
		Token char_literal98=null;
		Token char_literal100=null;
		Token char_literal101=null;
		Token string_literal103=null;
		Token string_literal104=null;
		Token ID105=null;
		Token char_literal106=null;
		Token char_literal108=null;
		Token char_literal109=null;
		Token string_literal111=null;
		Token string_literal118=null;
		Token string_literal121=null;
		Token string_literal123=null;
		Token string_literal124=null;
		Token ID125=null;
		Token char_literal126=null;
		Token char_literal128=null;
		Token string_literal129=null;
		Token string_literal130=null;
		Token ID131=null;
		Token char_literal132=null;
		Token char_literal134=null;
		ParserRuleReturnScope i =null;
		ParserRuleReturnScope v =null;
		ParserRuleReturnScope type81 =null;
		ParserRuleReturnScope expression83 =null;
		ParserRuleReturnScope expression90 =null;
		ParserRuleReturnScope expressions99 =null;
		ParserRuleReturnScope ids102 =null;
		ParserRuleReturnScope expressions107 =null;
		ParserRuleReturnScope label110 =null;
		ParserRuleReturnScope expression112 =null;
		ParserRuleReturnScope invariant113 =null;
		ParserRuleReturnScope modifies114 =null;
		ParserRuleReturnScope decreases115 =null;
		ParserRuleReturnScope relaxedBlock116 =null;
		ParserRuleReturnScope label117 =null;
		ParserRuleReturnScope expression119 =null;
		ParserRuleReturnScope relaxedBlock120 =null;
		ParserRuleReturnScope relaxedBlock122 =null;
		ParserRuleReturnScope expression127 =null;
		ParserRuleReturnScope expression133 =null;

		DafnyTree ass_tree=null;
		DafnyTree r_tree=null;
		DafnyTree f_tree=null;
		DafnyTree VAR78_tree=null;
		DafnyTree ID79_tree=null;
		DafnyTree char_literal80_tree=null;
		DafnyTree string_literal82_tree=null;
		DafnyTree char_literal84_tree=null;
		DafnyTree ID85_tree=null;
		DafnyTree char_literal86_tree=null;
		DafnyTree char_literal87_tree=null;
		DafnyTree ID88_tree=null;
		DafnyTree string_literal89_tree=null;
		DafnyTree char_literal91_tree=null;
		DafnyTree ID92_tree=null;
		DafnyTree char_literal93_tree=null;
		DafnyTree char_literal94_tree=null;
		DafnyTree char_literal95_tree=null;
		DafnyTree string_literal96_tree=null;
		DafnyTree string_literal97_tree=null;
		DafnyTree char_literal98_tree=null;
		DafnyTree char_literal100_tree=null;
		DafnyTree char_literal101_tree=null;
		DafnyTree string_literal103_tree=null;
		DafnyTree string_literal104_tree=null;
		DafnyTree ID105_tree=null;
		DafnyTree char_literal106_tree=null;
		DafnyTree char_literal108_tree=null;
		DafnyTree char_literal109_tree=null;
		DafnyTree string_literal111_tree=null;
		DafnyTree string_literal118_tree=null;
		DafnyTree string_literal121_tree=null;
		DafnyTree string_literal123_tree=null;
		DafnyTree string_literal124_tree=null;
		DafnyTree ID125_tree=null;
		DafnyTree char_literal126_tree=null;
		DafnyTree char_literal128_tree=null;
		DafnyTree string_literal129_tree=null;
		DafnyTree string_literal130_tree=null;
		DafnyTree ID131_tree=null;
		DafnyTree char_literal132_tree=null;
		DafnyTree char_literal134_tree=null;
		RewriteRuleTokenStream stream_67=new RewriteRuleTokenStream(adaptor,"token 67");
		RewriteRuleTokenStream stream_CALL=new RewriteRuleTokenStream(adaptor,"token CALL");
		RewriteRuleTokenStream stream_68=new RewriteRuleTokenStream(adaptor,"token 68");
		RewriteRuleTokenStream stream_TIMES=new RewriteRuleTokenStream(adaptor,"token TIMES");
		RewriteRuleTokenStream stream_71=new RewriteRuleTokenStream(adaptor,"token 71");
		RewriteRuleTokenStream stream_WHILE=new RewriteRuleTokenStream(adaptor,"token WHILE");
		RewriteRuleTokenStream stream_ID=new RewriteRuleTokenStream(adaptor,"token ID");
		RewriteRuleTokenStream stream_72=new RewriteRuleTokenStream(adaptor,"token 72");
		RewriteRuleTokenStream stream_ASSIGN=new RewriteRuleTokenStream(adaptor,"token ASSIGN");
		RewriteRuleTokenStream stream_73=new RewriteRuleTokenStream(adaptor,"token 73");
		RewriteRuleSubtreeStream stream_expression=new RewriteRuleSubtreeStream(adaptor,"rule expression");
		RewriteRuleSubtreeStream stream_decreases=new RewriteRuleSubtreeStream(adaptor,"rule decreases");
		RewriteRuleSubtreeStream stream_relaxedBlock=new RewriteRuleSubtreeStream(adaptor,"rule relaxedBlock");
		RewriteRuleSubtreeStream stream_modifies=new RewriteRuleSubtreeStream(adaptor,"rule modifies");
		RewriteRuleSubtreeStream stream_ids=new RewriteRuleSubtreeStream(adaptor,"rule ids");
		RewriteRuleSubtreeStream stream_label=new RewriteRuleSubtreeStream(adaptor,"rule label");
		RewriteRuleSubtreeStream stream_expressions=new RewriteRuleSubtreeStream(adaptor,"rule expressions");
		RewriteRuleSubtreeStream stream_invariant=new RewriteRuleSubtreeStream(adaptor,"rule invariant");

		try {
			// src/edu/kit/iti/algover/parser/Dafny.g:207:10: ( VAR ^ ID ':' ! type ( ':=' ! expression )? ';' !| ID ass= ':=' '*' ';' -> ^( HAVOC[$ass] ID ) | ID ':=' ^ expression ';' !| ID '[' i= expression ']' ass= ':=' v= expression ';' -> ^( ARRAY_UPDATE[$ass] ID $i $v) | ( ID ':=' 'call' )=>r= ID ':=' 'call' f= ID '(' ( expressions )? ')' ';' -> ^( 'call' $f ^( RESULTS $r) ^( ARGS ( expressions )? ) ) | ids ':=' 'call' ID '(' ( expressions )? ')' ';' -> ^( 'call' ID ^( RESULTS ids ) ^( ARGS ( expressions )? ) ) | ( label )? 'while' expression ( invariant )+ ( modifies )? decreases relaxedBlock -> ^( 'while' ( label )? expression ( invariant )+ ( modifies )? decreases relaxedBlock ) | ( label )? 'if' ^ expression relaxedBlock ( options {greedy=true; } : 'else' ! relaxedBlock )? | 'assert' ^ ( 'label' ! ID ':' !)? expression ';' !| 'assume' ^ ( 'label' ! ID ':' !)? expression ';' !)
			int alt29=10;
			switch ( input.LA(1) ) {
			case VAR:
				{
				alt29=1;
				}
				break;
			case ID:
				{
				switch ( input.LA(2) ) {
				case ASSIGN:
					{
					int LA29_8 = input.LA(3);
					if ( (LA29_8==TIMES) ) {
						alt29=2;
					}
					else if ( (LA29_8==CALL) && (synpred1_Dafny())) {
						alt29=5;
					}
					else if ( (LA29_8==BLOCK_BEGIN||LA29_8==ID||LA29_8==LIT||LA29_8==MINUS||(LA29_8 >= NOT && LA29_8 <= NULL)||LA29_8==THIS||LA29_8==67||LA29_8==72) ) {
						alt29=3;
					}

					else {
						if (state.backtracking>0) {state.failed=true; return retval;}
						int nvaeMark = input.mark();
						try {
							for (int nvaeConsume = 0; nvaeConsume < 3 - 1; nvaeConsume++) {
								input.consume();
							}
							NoViableAltException nvae =
								new NoViableAltException("", 29, 8, input);
							throw nvae;
						} finally {
							input.rewind(nvaeMark);
						}
					}

					}
					break;
				case 72:
					{
					alt29=4;
					}
					break;
				case 69:
					{
					alt29=6;
					}
					break;
				default:
					if (state.backtracking>0) {state.failed=true; return retval;}
					int nvaeMark = input.mark();
					try {
						input.consume();
						NoViableAltException nvae =
							new NoViableAltException("", 29, 2, input);
						throw nvae;
					} finally {
						input.rewind(nvaeMark);
					}
				}
				}
				break;
			case LABEL:
				{
				int LA29_3 = input.LA(2);
				if ( (LA29_3==ID) ) {
					int LA29_11 = input.LA(3);
					if ( (LA29_11==70) ) {
						int LA29_15 = input.LA(4);
						if ( (LA29_15==WHILE) ) {
							alt29=7;
						}
						else if ( (LA29_15==IF) ) {
							alt29=8;
						}

						else {
							if (state.backtracking>0) {state.failed=true; return retval;}
							int nvaeMark = input.mark();
							try {
								for (int nvaeConsume = 0; nvaeConsume < 4 - 1; nvaeConsume++) {
									input.consume();
								}
								NoViableAltException nvae =
									new NoViableAltException("", 29, 15, input);
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
								new NoViableAltException("", 29, 11, input);
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
							new NoViableAltException("", 29, 3, input);
						throw nvae;
					} finally {
						input.rewind(nvaeMark);
					}
				}

				}
				break;
			case WHILE:
				{
				alt29=7;
				}
				break;
			case IF:
				{
				alt29=8;
				}
				break;
			case ASSERT:
				{
				alt29=9;
				}
				break;
			case ASSUME:
				{
				alt29=10;
				}
				break;
			default:
				if (state.backtracking>0) {state.failed=true; return retval;}
				NoViableAltException nvae =
					new NoViableAltException("", 29, 0, input);
				throw nvae;
			}
			switch (alt29) {
				case 1 :
					// src/edu/kit/iti/algover/parser/Dafny.g:208:5: VAR ^ ID ':' ! type ( ':=' ! expression )? ';' !
					{
					root_0 = (DafnyTree)adaptor.nil();


					VAR78=(Token)match(input,VAR,FOLLOW_VAR_in_statement1130); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					VAR78_tree = (DafnyTree)adaptor.create(VAR78);
					root_0 = (DafnyTree)adaptor.becomeRoot(VAR78_tree, root_0);
					}

					ID79=(Token)match(input,ID,FOLLOW_ID_in_statement1133); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					ID79_tree = (DafnyTree)adaptor.create(ID79);
					adaptor.addChild(root_0, ID79_tree);
					}

					char_literal80=(Token)match(input,70,FOLLOW_70_in_statement1135); if (state.failed) return retval;
					pushFollow(FOLLOW_type_in_statement1138);
					type81=type();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, type81.getTree());

					// src/edu/kit/iti/algover/parser/Dafny.g:208:23: ( ':=' ! expression )?
					int alt19=2;
					int LA19_0 = input.LA(1);
					if ( (LA19_0==ASSIGN) ) {
						alt19=1;
					}
					switch (alt19) {
						case 1 :
							// src/edu/kit/iti/algover/parser/Dafny.g:208:24: ':=' ! expression
							{
							string_literal82=(Token)match(input,ASSIGN,FOLLOW_ASSIGN_in_statement1141); if (state.failed) return retval;
							pushFollow(FOLLOW_expression_in_statement1144);
							expression83=expression();
							state._fsp--;
							if (state.failed) return retval;
							if ( state.backtracking==0 ) adaptor.addChild(root_0, expression83.getTree());

							}
							break;

					}

					char_literal84=(Token)match(input,71,FOLLOW_71_in_statement1148); if (state.failed) return retval;
					}
					break;
				case 2 :
					// src/edu/kit/iti/algover/parser/Dafny.g:209:5: ID ass= ':=' '*' ';'
					{
					ID85=(Token)match(input,ID,FOLLOW_ID_in_statement1155); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_ID.add(ID85);

					ass=(Token)match(input,ASSIGN,FOLLOW_ASSIGN_in_statement1159); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_ASSIGN.add(ass);

					char_literal86=(Token)match(input,TIMES,FOLLOW_TIMES_in_statement1161); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_TIMES.add(char_literal86);

					char_literal87=(Token)match(input,71,FOLLOW_71_in_statement1163); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_71.add(char_literal87);

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
					// 209:25: -> ^( HAVOC[$ass] ID )
					{
						// src/edu/kit/iti/algover/parser/Dafny.g:209:28: ^( HAVOC[$ass] ID )
						{
						DafnyTree root_1 = (DafnyTree)adaptor.nil();
						root_1 = (DafnyTree)adaptor.becomeRoot((DafnyTree)adaptor.create(HAVOC, ass), root_1);
						adaptor.addChild(root_1, stream_ID.nextNode());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;
				case 3 :
					// src/edu/kit/iti/algover/parser/Dafny.g:210:5: ID ':=' ^ expression ';' !
					{
					root_0 = (DafnyTree)adaptor.nil();


					ID88=(Token)match(input,ID,FOLLOW_ID_in_statement1178); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					ID88_tree = (DafnyTree)adaptor.create(ID88);
					adaptor.addChild(root_0, ID88_tree);
					}

					string_literal89=(Token)match(input,ASSIGN,FOLLOW_ASSIGN_in_statement1180); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					string_literal89_tree = (DafnyTree)adaptor.create(string_literal89);
					root_0 = (DafnyTree)adaptor.becomeRoot(string_literal89_tree, root_0);
					}

					pushFollow(FOLLOW_expression_in_statement1183);
					expression90=expression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, expression90.getTree());

					char_literal91=(Token)match(input,71,FOLLOW_71_in_statement1185); if (state.failed) return retval;
					}
					break;
				case 4 :
					// src/edu/kit/iti/algover/parser/Dafny.g:211:5: ID '[' i= expression ']' ass= ':=' v= expression ';'
					{
					ID92=(Token)match(input,ID,FOLLOW_ID_in_statement1192); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_ID.add(ID92);

					char_literal93=(Token)match(input,72,FOLLOW_72_in_statement1194); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_72.add(char_literal93);

					pushFollow(FOLLOW_expression_in_statement1198);
					i=expression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_expression.add(i.getTree());
					char_literal94=(Token)match(input,73,FOLLOW_73_in_statement1200); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_73.add(char_literal94);

					ass=(Token)match(input,ASSIGN,FOLLOW_ASSIGN_in_statement1204); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_ASSIGN.add(ass);

					pushFollow(FOLLOW_expression_in_statement1208);
					v=expression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_expression.add(v.getTree());
					char_literal95=(Token)match(input,71,FOLLOW_71_in_statement1210); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_71.add(char_literal95);

					// AST REWRITE
					// elements: ID, v, i
					// token labels: 
					// rule labels: v, i, retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_v=new RewriteRuleSubtreeStream(adaptor,"rule v",v!=null?v.getTree():null);
					RewriteRuleSubtreeStream stream_i=new RewriteRuleSubtreeStream(adaptor,"rule i",i!=null?i.getTree():null);
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (DafnyTree)adaptor.nil();
					// 212:9: -> ^( ARRAY_UPDATE[$ass] ID $i $v)
					{
						// src/edu/kit/iti/algover/parser/Dafny.g:212:12: ^( ARRAY_UPDATE[$ass] ID $i $v)
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
					// src/edu/kit/iti/algover/parser/Dafny.g:213:5: ( ID ':=' 'call' )=>r= ID ':=' 'call' f= ID '(' ( expressions )? ')' ';'
					{
					r=(Token)match(input,ID,FOLLOW_ID_in_statement1251); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_ID.add(r);

					string_literal96=(Token)match(input,ASSIGN,FOLLOW_ASSIGN_in_statement1253); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_ASSIGN.add(string_literal96);

					string_literal97=(Token)match(input,CALL,FOLLOW_CALL_in_statement1255); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_CALL.add(string_literal97);

					f=(Token)match(input,ID,FOLLOW_ID_in_statement1259); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_ID.add(f);

					char_literal98=(Token)match(input,67,FOLLOW_67_in_statement1261); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_67.add(char_literal98);

					// src/edu/kit/iti/algover/parser/Dafny.g:213:51: ( expressions )?
					int alt20=2;
					int LA20_0 = input.LA(1);
					if ( (LA20_0==BLOCK_BEGIN||LA20_0==ID||LA20_0==LIT||LA20_0==MINUS||(LA20_0 >= NOT && LA20_0 <= NULL)||LA20_0==THIS||LA20_0==67||LA20_0==72) ) {
						alt20=1;
					}
					switch (alt20) {
						case 1 :
							// src/edu/kit/iti/algover/parser/Dafny.g:213:51: expressions
							{
							pushFollow(FOLLOW_expressions_in_statement1263);
							expressions99=expressions();
							state._fsp--;
							if (state.failed) return retval;
							if ( state.backtracking==0 ) stream_expressions.add(expressions99.getTree());
							}
							break;

					}

					char_literal100=(Token)match(input,68,FOLLOW_68_in_statement1266); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_68.add(char_literal100);

					char_literal101=(Token)match(input,71,FOLLOW_71_in_statement1268); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_71.add(char_literal101);

					// AST REWRITE
					// elements: expressions, CALL, f, r
					// token labels: r, f
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleTokenStream stream_r=new RewriteRuleTokenStream(adaptor,"token r",r);
					RewriteRuleTokenStream stream_f=new RewriteRuleTokenStream(adaptor,"token f",f);
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (DafnyTree)adaptor.nil();
					// 214:9: -> ^( 'call' $f ^( RESULTS $r) ^( ARGS ( expressions )? ) )
					{
						// src/edu/kit/iti/algover/parser/Dafny.g:214:12: ^( 'call' $f ^( RESULTS $r) ^( ARGS ( expressions )? ) )
						{
						DafnyTree root_1 = (DafnyTree)adaptor.nil();
						root_1 = (DafnyTree)adaptor.becomeRoot(stream_CALL.nextNode(), root_1);
						adaptor.addChild(root_1, stream_f.nextNode());
						// src/edu/kit/iti/algover/parser/Dafny.g:214:24: ^( RESULTS $r)
						{
						DafnyTree root_2 = (DafnyTree)adaptor.nil();
						root_2 = (DafnyTree)adaptor.becomeRoot((DafnyTree)adaptor.create(RESULTS, "RESULTS"), root_2);
						adaptor.addChild(root_2, stream_r.nextNode());
						adaptor.addChild(root_1, root_2);
						}

						// src/edu/kit/iti/algover/parser/Dafny.g:214:38: ^( ARGS ( expressions )? )
						{
						DafnyTree root_2 = (DafnyTree)adaptor.nil();
						root_2 = (DafnyTree)adaptor.becomeRoot((DafnyTree)adaptor.create(ARGS, "ARGS"), root_2);
						// src/edu/kit/iti/algover/parser/Dafny.g:214:45: ( expressions )?
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
					// src/edu/kit/iti/algover/parser/Dafny.g:215:5: ids ':=' 'call' ID '(' ( expressions )? ')' ';'
					{
					pushFollow(FOLLOW_ids_in_statement1305);
					ids102=ids();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_ids.add(ids102.getTree());
					string_literal103=(Token)match(input,ASSIGN,FOLLOW_ASSIGN_in_statement1307); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_ASSIGN.add(string_literal103);

					string_literal104=(Token)match(input,CALL,FOLLOW_CALL_in_statement1309); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_CALL.add(string_literal104);

					ID105=(Token)match(input,ID,FOLLOW_ID_in_statement1311); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_ID.add(ID105);

					char_literal106=(Token)match(input,67,FOLLOW_67_in_statement1313); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_67.add(char_literal106);

					// src/edu/kit/iti/algover/parser/Dafny.g:215:28: ( expressions )?
					int alt21=2;
					int LA21_0 = input.LA(1);
					if ( (LA21_0==BLOCK_BEGIN||LA21_0==ID||LA21_0==LIT||LA21_0==MINUS||(LA21_0 >= NOT && LA21_0 <= NULL)||LA21_0==THIS||LA21_0==67||LA21_0==72) ) {
						alt21=1;
					}
					switch (alt21) {
						case 1 :
							// src/edu/kit/iti/algover/parser/Dafny.g:215:28: expressions
							{
							pushFollow(FOLLOW_expressions_in_statement1315);
							expressions107=expressions();
							state._fsp--;
							if (state.failed) return retval;
							if ( state.backtracking==0 ) stream_expressions.add(expressions107.getTree());
							}
							break;

					}

					char_literal108=(Token)match(input,68,FOLLOW_68_in_statement1318); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_68.add(char_literal108);

					char_literal109=(Token)match(input,71,FOLLOW_71_in_statement1320); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_71.add(char_literal109);

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

					root_0 = (DafnyTree)adaptor.nil();
					// 216:9: -> ^( 'call' ID ^( RESULTS ids ) ^( ARGS ( expressions )? ) )
					{
						// src/edu/kit/iti/algover/parser/Dafny.g:216:12: ^( 'call' ID ^( RESULTS ids ) ^( ARGS ( expressions )? ) )
						{
						DafnyTree root_1 = (DafnyTree)adaptor.nil();
						root_1 = (DafnyTree)adaptor.becomeRoot(stream_CALL.nextNode(), root_1);
						adaptor.addChild(root_1, stream_ID.nextNode());
						// src/edu/kit/iti/algover/parser/Dafny.g:216:24: ^( RESULTS ids )
						{
						DafnyTree root_2 = (DafnyTree)adaptor.nil();
						root_2 = (DafnyTree)adaptor.becomeRoot((DafnyTree)adaptor.create(RESULTS, "RESULTS"), root_2);
						adaptor.addChild(root_2, stream_ids.nextTree());
						adaptor.addChild(root_1, root_2);
						}

						// src/edu/kit/iti/algover/parser/Dafny.g:216:39: ^( ARGS ( expressions )? )
						{
						DafnyTree root_2 = (DafnyTree)adaptor.nil();
						root_2 = (DafnyTree)adaptor.becomeRoot((DafnyTree)adaptor.create(ARGS, "ARGS"), root_2);
						// src/edu/kit/iti/algover/parser/Dafny.g:216:46: ( expressions )?
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
					// src/edu/kit/iti/algover/parser/Dafny.g:217:5: ( label )? 'while' expression ( invariant )+ ( modifies )? decreases relaxedBlock
					{
					// src/edu/kit/iti/algover/parser/Dafny.g:217:5: ( label )?
					int alt22=2;
					int LA22_0 = input.LA(1);
					if ( (LA22_0==LABEL) ) {
						alt22=1;
					}
					switch (alt22) {
						case 1 :
							// src/edu/kit/iti/algover/parser/Dafny.g:217:5: label
							{
							pushFollow(FOLLOW_label_in_statement1355);
							label110=label();
							state._fsp--;
							if (state.failed) return retval;
							if ( state.backtracking==0 ) stream_label.add(label110.getTree());
							}
							break;

					}

					string_literal111=(Token)match(input,WHILE,FOLLOW_WHILE_in_statement1364); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_WHILE.add(string_literal111);

					pushFollow(FOLLOW_expression_in_statement1366);
					expression112=expression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_expression.add(expression112.getTree());
					// src/edu/kit/iti/algover/parser/Dafny.g:218:26: ( invariant )+
					int cnt23=0;
					loop23:
					while (true) {
						int alt23=2;
						int LA23_0 = input.LA(1);
						if ( (LA23_0==INVARIANT) ) {
							alt23=1;
						}

						switch (alt23) {
						case 1 :
							// src/edu/kit/iti/algover/parser/Dafny.g:218:26: invariant
							{
							pushFollow(FOLLOW_invariant_in_statement1368);
							invariant113=invariant();
							state._fsp--;
							if (state.failed) return retval;
							if ( state.backtracking==0 ) stream_invariant.add(invariant113.getTree());
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

					// src/edu/kit/iti/algover/parser/Dafny.g:218:37: ( modifies )?
					int alt24=2;
					int LA24_0 = input.LA(1);
					if ( (LA24_0==MODIFIES) ) {
						alt24=1;
					}
					switch (alt24) {
						case 1 :
							// src/edu/kit/iti/algover/parser/Dafny.g:218:37: modifies
							{
							pushFollow(FOLLOW_modifies_in_statement1371);
							modifies114=modifies();
							state._fsp--;
							if (state.failed) return retval;
							if ( state.backtracking==0 ) stream_modifies.add(modifies114.getTree());
							}
							break;

					}

					pushFollow(FOLLOW_decreases_in_statement1374);
					decreases115=decreases();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_decreases.add(decreases115.getTree());
					pushFollow(FOLLOW_relaxedBlock_in_statement1376);
					relaxedBlock116=relaxedBlock();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_relaxedBlock.add(relaxedBlock116.getTree());
					// AST REWRITE
					// elements: label, relaxedBlock, decreases, invariant, modifies, WHILE, expression
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (DafnyTree)adaptor.nil();
					// 219:9: -> ^( 'while' ( label )? expression ( invariant )+ ( modifies )? decreases relaxedBlock )
					{
						// src/edu/kit/iti/algover/parser/Dafny.g:219:12: ^( 'while' ( label )? expression ( invariant )+ ( modifies )? decreases relaxedBlock )
						{
						DafnyTree root_1 = (DafnyTree)adaptor.nil();
						root_1 = (DafnyTree)adaptor.becomeRoot(stream_WHILE.nextNode(), root_1);
						// src/edu/kit/iti/algover/parser/Dafny.g:219:22: ( label )?
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

						// src/edu/kit/iti/algover/parser/Dafny.g:219:51: ( modifies )?
						if ( stream_modifies.hasNext() ) {
							adaptor.addChild(root_1, stream_modifies.nextTree());
						}
						stream_modifies.reset();

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
					// src/edu/kit/iti/algover/parser/Dafny.g:220:5: ( label )? 'if' ^ expression relaxedBlock ( options {greedy=true; } : 'else' ! relaxedBlock )?
					{
					root_0 = (DafnyTree)adaptor.nil();


					// src/edu/kit/iti/algover/parser/Dafny.g:220:5: ( label )?
					int alt25=2;
					int LA25_0 = input.LA(1);
					if ( (LA25_0==LABEL) ) {
						alt25=1;
					}
					switch (alt25) {
						case 1 :
							// src/edu/kit/iti/algover/parser/Dafny.g:220:5: label
							{
							pushFollow(FOLLOW_label_in_statement1411);
							label117=label();
							state._fsp--;
							if (state.failed) return retval;
							if ( state.backtracking==0 ) adaptor.addChild(root_0, label117.getTree());

							}
							break;

					}

					string_literal118=(Token)match(input,IF,FOLLOW_IF_in_statement1414); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					string_literal118_tree = (DafnyTree)adaptor.create(string_literal118);
					root_0 = (DafnyTree)adaptor.becomeRoot(string_literal118_tree, root_0);
					}

					pushFollow(FOLLOW_expression_in_statement1417);
					expression119=expression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, expression119.getTree());

					pushFollow(FOLLOW_relaxedBlock_in_statement1419);
					relaxedBlock120=relaxedBlock();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, relaxedBlock120.getTree());

					// src/edu/kit/iti/algover/parser/Dafny.g:221:7: ( options {greedy=true; } : 'else' ! relaxedBlock )?
					int alt26=2;
					int LA26_0 = input.LA(1);
					if ( (LA26_0==ELSE) ) {
						alt26=1;
					}
					switch (alt26) {
						case 1 :
							// src/edu/kit/iti/algover/parser/Dafny.g:221:36: 'else' ! relaxedBlock
							{
							string_literal121=(Token)match(input,ELSE,FOLLOW_ELSE_in_statement1440); if (state.failed) return retval;
							pushFollow(FOLLOW_relaxedBlock_in_statement1443);
							relaxedBlock122=relaxedBlock();
							state._fsp--;
							if (state.failed) return retval;
							if ( state.backtracking==0 ) adaptor.addChild(root_0, relaxedBlock122.getTree());

							}
							break;

					}

					}
					break;
				case 9 :
					// src/edu/kit/iti/algover/parser/Dafny.g:222:5: 'assert' ^ ( 'label' ! ID ':' !)? expression ';' !
					{
					root_0 = (DafnyTree)adaptor.nil();


					string_literal123=(Token)match(input,ASSERT,FOLLOW_ASSERT_in_statement1452); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					string_literal123_tree = (DafnyTree)adaptor.create(string_literal123);
					root_0 = (DafnyTree)adaptor.becomeRoot(string_literal123_tree, root_0);
					}

					// src/edu/kit/iti/algover/parser/Dafny.g:222:15: ( 'label' ! ID ':' !)?
					int alt27=2;
					int LA27_0 = input.LA(1);
					if ( (LA27_0==LABEL) ) {
						alt27=1;
					}
					switch (alt27) {
						case 1 :
							// src/edu/kit/iti/algover/parser/Dafny.g:222:17: 'label' ! ID ':' !
							{
							string_literal124=(Token)match(input,LABEL,FOLLOW_LABEL_in_statement1457); if (state.failed) return retval;
							ID125=(Token)match(input,ID,FOLLOW_ID_in_statement1460); if (state.failed) return retval;
							if ( state.backtracking==0 ) {
							ID125_tree = (DafnyTree)adaptor.create(ID125);
							adaptor.addChild(root_0, ID125_tree);
							}

							char_literal126=(Token)match(input,70,FOLLOW_70_in_statement1462); if (state.failed) return retval;
							}
							break;

					}

					pushFollow(FOLLOW_expression_in_statement1468);
					expression127=expression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, expression127.getTree());

					char_literal128=(Token)match(input,71,FOLLOW_71_in_statement1470); if (state.failed) return retval;
					}
					break;
				case 10 :
					// src/edu/kit/iti/algover/parser/Dafny.g:223:5: 'assume' ^ ( 'label' ! ID ':' !)? expression ';' !
					{
					root_0 = (DafnyTree)adaptor.nil();


					string_literal129=(Token)match(input,ASSUME,FOLLOW_ASSUME_in_statement1477); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					string_literal129_tree = (DafnyTree)adaptor.create(string_literal129);
					root_0 = (DafnyTree)adaptor.becomeRoot(string_literal129_tree, root_0);
					}

					// src/edu/kit/iti/algover/parser/Dafny.g:223:15: ( 'label' ! ID ':' !)?
					int alt28=2;
					int LA28_0 = input.LA(1);
					if ( (LA28_0==LABEL) ) {
						alt28=1;
					}
					switch (alt28) {
						case 1 :
							// src/edu/kit/iti/algover/parser/Dafny.g:223:17: 'label' ! ID ':' !
							{
							string_literal130=(Token)match(input,LABEL,FOLLOW_LABEL_in_statement1482); if (state.failed) return retval;
							ID131=(Token)match(input,ID,FOLLOW_ID_in_statement1485); if (state.failed) return retval;
							if ( state.backtracking==0 ) {
							ID131_tree = (DafnyTree)adaptor.create(ID131);
							adaptor.addChild(root_0, ID131_tree);
							}

							char_literal132=(Token)match(input,70,FOLLOW_70_in_statement1487); if (state.failed) return retval;
							}
							break;

					}

					pushFollow(FOLLOW_expression_in_statement1493);
					expression133=expression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, expression133.getTree());

					char_literal134=(Token)match(input,71,FOLLOW_71_in_statement1495); if (state.failed) return retval;
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
	// src/edu/kit/iti/algover/parser/Dafny.g:226:1: ids : ID ( ',' ! ID )+ ;
	public final DafnyParser.ids_return ids() throws RecognitionException {
		DafnyParser.ids_return retval = new DafnyParser.ids_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		Token ID135=null;
		Token char_literal136=null;
		Token ID137=null;

		DafnyTree ID135_tree=null;
		DafnyTree char_literal136_tree=null;
		DafnyTree ID137_tree=null;

		try {
			// src/edu/kit/iti/algover/parser/Dafny.g:226:4: ( ID ( ',' ! ID )+ )
			// src/edu/kit/iti/algover/parser/Dafny.g:227:3: ID ( ',' ! ID )+
			{
			root_0 = (DafnyTree)adaptor.nil();


			ID135=(Token)match(input,ID,FOLLOW_ID_in_ids1508); if (state.failed) return retval;
			if ( state.backtracking==0 ) {
			ID135_tree = (DafnyTree)adaptor.create(ID135);
			adaptor.addChild(root_0, ID135_tree);
			}

			// src/edu/kit/iti/algover/parser/Dafny.g:227:6: ( ',' ! ID )+
			int cnt30=0;
			loop30:
			while (true) {
				int alt30=2;
				int LA30_0 = input.LA(1);
				if ( (LA30_0==69) ) {
					alt30=1;
				}

				switch (alt30) {
				case 1 :
					// src/edu/kit/iti/algover/parser/Dafny.g:227:7: ',' ! ID
					{
					char_literal136=(Token)match(input,69,FOLLOW_69_in_ids1511); if (state.failed) return retval;
					ID137=(Token)match(input,ID,FOLLOW_ID_in_ids1514); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					ID137_tree = (DafnyTree)adaptor.create(ID137);
					adaptor.addChild(root_0, ID137_tree);
					}

					}
					break;

				default :
					if ( cnt30 >= 1 ) break loop30;
					if (state.backtracking>0) {state.failed=true; return retval;}
					EarlyExitException eee = new EarlyExitException(30, input);
					throw eee;
				}
				cnt30++;
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
	// src/edu/kit/iti/algover/parser/Dafny.g:230:1: expressions : expression ( ',' ! expression )* ;
	public final DafnyParser.expressions_return expressions() throws RecognitionException {
		DafnyParser.expressions_return retval = new DafnyParser.expressions_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		Token char_literal139=null;
		ParserRuleReturnScope expression138 =null;
		ParserRuleReturnScope expression140 =null;

		DafnyTree char_literal139_tree=null;

		try {
			// src/edu/kit/iti/algover/parser/Dafny.g:230:12: ( expression ( ',' ! expression )* )
			// src/edu/kit/iti/algover/parser/Dafny.g:231:3: expression ( ',' ! expression )*
			{
			root_0 = (DafnyTree)adaptor.nil();


			pushFollow(FOLLOW_expression_in_expressions1528);
			expression138=expression();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, expression138.getTree());

			// src/edu/kit/iti/algover/parser/Dafny.g:231:14: ( ',' ! expression )*
			loop31:
			while (true) {
				int alt31=2;
				int LA31_0 = input.LA(1);
				if ( (LA31_0==69) ) {
					alt31=1;
				}

				switch (alt31) {
				case 1 :
					// src/edu/kit/iti/algover/parser/Dafny.g:231:16: ',' ! expression
					{
					char_literal139=(Token)match(input,69,FOLLOW_69_in_expressions1532); if (state.failed) return retval;
					pushFollow(FOLLOW_expression_in_expressions1535);
					expression140=expression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, expression140.getTree());

					}
					break;

				default :
					break loop31;
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
	// src/edu/kit/iti/algover/parser/Dafny.g:234:1: expression : or_expr ;
	public final DafnyParser.expression_return expression() throws RecognitionException {
		DafnyParser.expression_return retval = new DafnyParser.expression_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		ParserRuleReturnScope or_expr141 =null;


		try {
			// src/edu/kit/iti/algover/parser/Dafny.g:234:11: ( or_expr )
			// src/edu/kit/iti/algover/parser/Dafny.g:235:3: or_expr
			{
			root_0 = (DafnyTree)adaptor.nil();


			pushFollow(FOLLOW_or_expr_in_expression1550);
			or_expr141=or_expr();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, or_expr141.getTree());

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
	// src/edu/kit/iti/algover/parser/Dafny.g:237:1: or_expr : and_expr ( ( '||' ^| '==>' ^) or_expr )? ;
	public final DafnyParser.or_expr_return or_expr() throws RecognitionException {
		DafnyParser.or_expr_return retval = new DafnyParser.or_expr_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		Token string_literal143=null;
		Token string_literal144=null;
		ParserRuleReturnScope and_expr142 =null;
		ParserRuleReturnScope or_expr145 =null;

		DafnyTree string_literal143_tree=null;
		DafnyTree string_literal144_tree=null;

		try {
			// src/edu/kit/iti/algover/parser/Dafny.g:237:8: ( and_expr ( ( '||' ^| '==>' ^) or_expr )? )
			// src/edu/kit/iti/algover/parser/Dafny.g:238:3: and_expr ( ( '||' ^| '==>' ^) or_expr )?
			{
			root_0 = (DafnyTree)adaptor.nil();


			pushFollow(FOLLOW_and_expr_in_or_expr1559);
			and_expr142=and_expr();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, and_expr142.getTree());

			// src/edu/kit/iti/algover/parser/Dafny.g:238:12: ( ( '||' ^| '==>' ^) or_expr )?
			int alt33=2;
			int LA33_0 = input.LA(1);
			if ( (LA33_0==IMPLIES||LA33_0==OR) ) {
				alt33=1;
			}
			switch (alt33) {
				case 1 :
					// src/edu/kit/iti/algover/parser/Dafny.g:238:14: ( '||' ^| '==>' ^) or_expr
					{
					// src/edu/kit/iti/algover/parser/Dafny.g:238:14: ( '||' ^| '==>' ^)
					int alt32=2;
					int LA32_0 = input.LA(1);
					if ( (LA32_0==OR) ) {
						alt32=1;
					}
					else if ( (LA32_0==IMPLIES) ) {
						alt32=2;
					}

					else {
						if (state.backtracking>0) {state.failed=true; return retval;}
						NoViableAltException nvae =
							new NoViableAltException("", 32, 0, input);
						throw nvae;
					}

					switch (alt32) {
						case 1 :
							// src/edu/kit/iti/algover/parser/Dafny.g:238:15: '||' ^
							{
							string_literal143=(Token)match(input,OR,FOLLOW_OR_in_or_expr1564); if (state.failed) return retval;
							if ( state.backtracking==0 ) {
							string_literal143_tree = (DafnyTree)adaptor.create(string_literal143);
							root_0 = (DafnyTree)adaptor.becomeRoot(string_literal143_tree, root_0);
							}

							}
							break;
						case 2 :
							// src/edu/kit/iti/algover/parser/Dafny.g:238:23: '==>' ^
							{
							string_literal144=(Token)match(input,IMPLIES,FOLLOW_IMPLIES_in_or_expr1569); if (state.failed) return retval;
							if ( state.backtracking==0 ) {
							string_literal144_tree = (DafnyTree)adaptor.create(string_literal144);
							root_0 = (DafnyTree)adaptor.becomeRoot(string_literal144_tree, root_0);
							}

							}
							break;

					}

					pushFollow(FOLLOW_or_expr_in_or_expr1573);
					or_expr145=or_expr();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, or_expr145.getTree());

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
	// src/edu/kit/iti/algover/parser/Dafny.g:241:1: and_expr : rel_expr ( '&&' ^ and_expr )? ;
	public final DafnyParser.and_expr_return and_expr() throws RecognitionException {
		DafnyParser.and_expr_return retval = new DafnyParser.and_expr_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		Token string_literal147=null;
		ParserRuleReturnScope rel_expr146 =null;
		ParserRuleReturnScope and_expr148 =null;

		DafnyTree string_literal147_tree=null;

		try {
			// src/edu/kit/iti/algover/parser/Dafny.g:241:9: ( rel_expr ( '&&' ^ and_expr )? )
			// src/edu/kit/iti/algover/parser/Dafny.g:242:3: rel_expr ( '&&' ^ and_expr )?
			{
			root_0 = (DafnyTree)adaptor.nil();


			pushFollow(FOLLOW_rel_expr_in_and_expr1588);
			rel_expr146=rel_expr();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, rel_expr146.getTree());

			// src/edu/kit/iti/algover/parser/Dafny.g:242:12: ( '&&' ^ and_expr )?
			int alt34=2;
			int LA34_0 = input.LA(1);
			if ( (LA34_0==AND) ) {
				alt34=1;
			}
			switch (alt34) {
				case 1 :
					// src/edu/kit/iti/algover/parser/Dafny.g:242:14: '&&' ^ and_expr
					{
					string_literal147=(Token)match(input,AND,FOLLOW_AND_in_and_expr1592); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					string_literal147_tree = (DafnyTree)adaptor.create(string_literal147);
					root_0 = (DafnyTree)adaptor.becomeRoot(string_literal147_tree, root_0);
					}

					pushFollow(FOLLOW_and_expr_in_and_expr1595);
					and_expr148=and_expr();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, and_expr148.getTree());

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
	// src/edu/kit/iti/algover/parser/Dafny.g:245:1: rel_expr : add_expr ( ( '<' ^| '>' ^| '==' ^| '!=' ^| '<=' ^| '>=' ^) add_expr )? ;
	public final DafnyParser.rel_expr_return rel_expr() throws RecognitionException {
		DafnyParser.rel_expr_return retval = new DafnyParser.rel_expr_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		Token char_literal150=null;
		Token char_literal151=null;
		Token string_literal152=null;
		Token string_literal153=null;
		Token string_literal154=null;
		Token string_literal155=null;
		ParserRuleReturnScope add_expr149 =null;
		ParserRuleReturnScope add_expr156 =null;

		DafnyTree char_literal150_tree=null;
		DafnyTree char_literal151_tree=null;
		DafnyTree string_literal152_tree=null;
		DafnyTree string_literal153_tree=null;
		DafnyTree string_literal154_tree=null;
		DafnyTree string_literal155_tree=null;

		try {
			// src/edu/kit/iti/algover/parser/Dafny.g:245:9: ( add_expr ( ( '<' ^| '>' ^| '==' ^| '!=' ^| '<=' ^| '>=' ^) add_expr )? )
			// src/edu/kit/iti/algover/parser/Dafny.g:246:3: add_expr ( ( '<' ^| '>' ^| '==' ^| '!=' ^| '<=' ^| '>=' ^) add_expr )?
			{
			root_0 = (DafnyTree)adaptor.nil();


			pushFollow(FOLLOW_add_expr_in_rel_expr1610);
			add_expr149=add_expr();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, add_expr149.getTree());

			// src/edu/kit/iti/algover/parser/Dafny.g:246:12: ( ( '<' ^| '>' ^| '==' ^| '!=' ^| '<=' ^| '>=' ^) add_expr )?
			int alt36=2;
			int LA36_0 = input.LA(1);
			if ( (LA36_0==EQ||(LA36_0 >= GE && LA36_0 <= GT)||LA36_0==LE||LA36_0==LT||LA36_0==NEQ) ) {
				alt36=1;
			}
			switch (alt36) {
				case 1 :
					// src/edu/kit/iti/algover/parser/Dafny.g:246:14: ( '<' ^| '>' ^| '==' ^| '!=' ^| '<=' ^| '>=' ^) add_expr
					{
					// src/edu/kit/iti/algover/parser/Dafny.g:246:14: ( '<' ^| '>' ^| '==' ^| '!=' ^| '<=' ^| '>=' ^)
					int alt35=6;
					switch ( input.LA(1) ) {
					case LT:
						{
						alt35=1;
						}
						break;
					case GT:
						{
						alt35=2;
						}
						break;
					case EQ:
						{
						alt35=3;
						}
						break;
					case NEQ:
						{
						alt35=4;
						}
						break;
					case LE:
						{
						alt35=5;
						}
						break;
					case GE:
						{
						alt35=6;
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
							// src/edu/kit/iti/algover/parser/Dafny.g:246:15: '<' ^
							{
							char_literal150=(Token)match(input,LT,FOLLOW_LT_in_rel_expr1615); if (state.failed) return retval;
							if ( state.backtracking==0 ) {
							char_literal150_tree = (DafnyTree)adaptor.create(char_literal150);
							root_0 = (DafnyTree)adaptor.becomeRoot(char_literal150_tree, root_0);
							}

							}
							break;
						case 2 :
							// src/edu/kit/iti/algover/parser/Dafny.g:246:22: '>' ^
							{
							char_literal151=(Token)match(input,GT,FOLLOW_GT_in_rel_expr1620); if (state.failed) return retval;
							if ( state.backtracking==0 ) {
							char_literal151_tree = (DafnyTree)adaptor.create(char_literal151);
							root_0 = (DafnyTree)adaptor.becomeRoot(char_literal151_tree, root_0);
							}

							}
							break;
						case 3 :
							// src/edu/kit/iti/algover/parser/Dafny.g:246:29: '==' ^
							{
							string_literal152=(Token)match(input,EQ,FOLLOW_EQ_in_rel_expr1625); if (state.failed) return retval;
							if ( state.backtracking==0 ) {
							string_literal152_tree = (DafnyTree)adaptor.create(string_literal152);
							root_0 = (DafnyTree)adaptor.becomeRoot(string_literal152_tree, root_0);
							}

							}
							break;
						case 4 :
							// src/edu/kit/iti/algover/parser/Dafny.g:246:37: '!=' ^
							{
							string_literal153=(Token)match(input,NEQ,FOLLOW_NEQ_in_rel_expr1630); if (state.failed) return retval;
							if ( state.backtracking==0 ) {
							string_literal153_tree = (DafnyTree)adaptor.create(string_literal153);
							root_0 = (DafnyTree)adaptor.becomeRoot(string_literal153_tree, root_0);
							}

							}
							break;
						case 5 :
							// src/edu/kit/iti/algover/parser/Dafny.g:246:45: '<=' ^
							{
							string_literal154=(Token)match(input,LE,FOLLOW_LE_in_rel_expr1635); if (state.failed) return retval;
							if ( state.backtracking==0 ) {
							string_literal154_tree = (DafnyTree)adaptor.create(string_literal154);
							root_0 = (DafnyTree)adaptor.becomeRoot(string_literal154_tree, root_0);
							}

							}
							break;
						case 6 :
							// src/edu/kit/iti/algover/parser/Dafny.g:246:53: '>=' ^
							{
							string_literal155=(Token)match(input,GE,FOLLOW_GE_in_rel_expr1640); if (state.failed) return retval;
							if ( state.backtracking==0 ) {
							string_literal155_tree = (DafnyTree)adaptor.create(string_literal155);
							root_0 = (DafnyTree)adaptor.becomeRoot(string_literal155_tree, root_0);
							}

							}
							break;

					}

					pushFollow(FOLLOW_add_expr_in_rel_expr1644);
					add_expr156=add_expr();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, add_expr156.getTree());

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
	// src/edu/kit/iti/algover/parser/Dafny.g:249:1: add_expr : mul_expr ( ( '+' | '-' | '++' ) ^ add_expr )? ;
	public final DafnyParser.add_expr_return add_expr() throws RecognitionException {
		DafnyParser.add_expr_return retval = new DafnyParser.add_expr_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		Token set158=null;
		ParserRuleReturnScope mul_expr157 =null;
		ParserRuleReturnScope add_expr159 =null;

		DafnyTree set158_tree=null;

		try {
			// src/edu/kit/iti/algover/parser/Dafny.g:249:9: ( mul_expr ( ( '+' | '-' | '++' ) ^ add_expr )? )
			// src/edu/kit/iti/algover/parser/Dafny.g:250:3: mul_expr ( ( '+' | '-' | '++' ) ^ add_expr )?
			{
			root_0 = (DafnyTree)adaptor.nil();


			pushFollow(FOLLOW_mul_expr_in_add_expr1659);
			mul_expr157=mul_expr();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, mul_expr157.getTree());

			// src/edu/kit/iti/algover/parser/Dafny.g:250:12: ( ( '+' | '-' | '++' ) ^ add_expr )?
			int alt37=2;
			int LA37_0 = input.LA(1);
			if ( (LA37_0==MINUS||LA37_0==PLUS||LA37_0==UNION) ) {
				alt37=1;
			}
			switch (alt37) {
				case 1 :
					// src/edu/kit/iti/algover/parser/Dafny.g:250:14: ( '+' | '-' | '++' ) ^ add_expr
					{
					set158=input.LT(1);
					set158=input.LT(1);
					if ( input.LA(1)==MINUS||input.LA(1)==PLUS||input.LA(1)==UNION ) {
						input.consume();
						if ( state.backtracking==0 ) root_0 = (DafnyTree)adaptor.becomeRoot((DafnyTree)adaptor.create(set158), root_0);
						state.errorRecovery=false;
						state.failed=false;
					}
					else {
						if (state.backtracking>0) {state.failed=true; return retval;}
						MismatchedSetException mse = new MismatchedSetException(null,input);
						throw mse;
					}
					pushFollow(FOLLOW_add_expr_in_add_expr1676);
					add_expr159=add_expr();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, add_expr159.getTree());

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
	// src/edu/kit/iti/algover/parser/Dafny.g:253:1: mul_expr : prefix_expr ( ( '*' | '**' ) ^ mul_expr )? ;
	public final DafnyParser.mul_expr_return mul_expr() throws RecognitionException {
		DafnyParser.mul_expr_return retval = new DafnyParser.mul_expr_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		Token set161=null;
		ParserRuleReturnScope prefix_expr160 =null;
		ParserRuleReturnScope mul_expr162 =null;

		DafnyTree set161_tree=null;

		try {
			// src/edu/kit/iti/algover/parser/Dafny.g:253:9: ( prefix_expr ( ( '*' | '**' ) ^ mul_expr )? )
			// src/edu/kit/iti/algover/parser/Dafny.g:254:3: prefix_expr ( ( '*' | '**' ) ^ mul_expr )?
			{
			root_0 = (DafnyTree)adaptor.nil();


			pushFollow(FOLLOW_prefix_expr_in_mul_expr1691);
			prefix_expr160=prefix_expr();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, prefix_expr160.getTree());

			// src/edu/kit/iti/algover/parser/Dafny.g:254:15: ( ( '*' | '**' ) ^ mul_expr )?
			int alt38=2;
			int LA38_0 = input.LA(1);
			if ( (LA38_0==INTERSECT||LA38_0==TIMES) ) {
				alt38=1;
			}
			switch (alt38) {
				case 1 :
					// src/edu/kit/iti/algover/parser/Dafny.g:254:17: ( '*' | '**' ) ^ mul_expr
					{
					set161=input.LT(1);
					set161=input.LT(1);
					if ( input.LA(1)==INTERSECT||input.LA(1)==TIMES ) {
						input.consume();
						if ( state.backtracking==0 ) root_0 = (DafnyTree)adaptor.becomeRoot((DafnyTree)adaptor.create(set161), root_0);
						state.errorRecovery=false;
						state.failed=false;
					}
					else {
						if (state.backtracking>0) {state.failed=true; return retval;}
						MismatchedSetException mse = new MismatchedSetException(null,input);
						throw mse;
					}
					pushFollow(FOLLOW_mul_expr_in_mul_expr1704);
					mul_expr162=mul_expr();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, mul_expr162.getTree());

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
	// src/edu/kit/iti/algover/parser/Dafny.g:257:1: prefix_expr : ( '-' ^ prefix_expr | '!' ^ prefix_expr | postfix_expr );
	public final DafnyParser.prefix_expr_return prefix_expr() throws RecognitionException {
		DafnyParser.prefix_expr_return retval = new DafnyParser.prefix_expr_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		Token char_literal163=null;
		Token char_literal165=null;
		ParserRuleReturnScope prefix_expr164 =null;
		ParserRuleReturnScope prefix_expr166 =null;
		ParserRuleReturnScope postfix_expr167 =null;

		DafnyTree char_literal163_tree=null;
		DafnyTree char_literal165_tree=null;

		try {
			// src/edu/kit/iti/algover/parser/Dafny.g:257:12: ( '-' ^ prefix_expr | '!' ^ prefix_expr | postfix_expr )
			int alt39=3;
			switch ( input.LA(1) ) {
			case MINUS:
				{
				alt39=1;
				}
				break;
			case NOT:
				{
				alt39=2;
				}
				break;
			case BLOCK_BEGIN:
			case ID:
			case LIT:
			case NULL:
			case THIS:
			case 67:
			case 72:
				{
				alt39=3;
				}
				break;
			default:
				if (state.backtracking>0) {state.failed=true; return retval;}
				NoViableAltException nvae =
					new NoViableAltException("", 39, 0, input);
				throw nvae;
			}
			switch (alt39) {
				case 1 :
					// src/edu/kit/iti/algover/parser/Dafny.g:258:5: '-' ^ prefix_expr
					{
					root_0 = (DafnyTree)adaptor.nil();


					char_literal163=(Token)match(input,MINUS,FOLLOW_MINUS_in_prefix_expr1721); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					char_literal163_tree = (DafnyTree)adaptor.create(char_literal163);
					root_0 = (DafnyTree)adaptor.becomeRoot(char_literal163_tree, root_0);
					}

					pushFollow(FOLLOW_prefix_expr_in_prefix_expr1724);
					prefix_expr164=prefix_expr();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, prefix_expr164.getTree());

					}
					break;
				case 2 :
					// src/edu/kit/iti/algover/parser/Dafny.g:259:5: '!' ^ prefix_expr
					{
					root_0 = (DafnyTree)adaptor.nil();


					char_literal165=(Token)match(input,NOT,FOLLOW_NOT_in_prefix_expr1730); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					char_literal165_tree = (DafnyTree)adaptor.create(char_literal165);
					root_0 = (DafnyTree)adaptor.becomeRoot(char_literal165_tree, root_0);
					}

					pushFollow(FOLLOW_prefix_expr_in_prefix_expr1733);
					prefix_expr166=prefix_expr();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, prefix_expr166.getTree());

					}
					break;
				case 3 :
					// src/edu/kit/iti/algover/parser/Dafny.g:260:5: postfix_expr
					{
					root_0 = (DafnyTree)adaptor.nil();


					pushFollow(FOLLOW_postfix_expr_in_prefix_expr1739);
					postfix_expr167=postfix_expr();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, postfix_expr167.getTree());

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
	// src/edu/kit/iti/algover/parser/Dafny.g:263:1: postfix_expr : ( atom_expr -> atom_expr ) ( '[' expression ']' -> ^( ARRAY_ACCESS atom_expr expression ) | '.' LENGTH -> ^( LENGTH atom_expr ) | '.' ID '(' expressions ')' -> ^( OBJ_FUNC_CALL ID atom_expr expressions ) | '.' ID -> ^( FIELD_ACCESS atom_expr ID ) )* ;
	public final DafnyParser.postfix_expr_return postfix_expr() throws RecognitionException {
		DafnyParser.postfix_expr_return retval = new DafnyParser.postfix_expr_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		Token char_literal169=null;
		Token char_literal171=null;
		Token char_literal172=null;
		Token LENGTH173=null;
		Token char_literal174=null;
		Token ID175=null;
		Token char_literal176=null;
		Token char_literal178=null;
		Token char_literal179=null;
		Token ID180=null;
		ParserRuleReturnScope atom_expr168 =null;
		ParserRuleReturnScope expression170 =null;
		ParserRuleReturnScope expressions177 =null;

		DafnyTree char_literal169_tree=null;
		DafnyTree char_literal171_tree=null;
		DafnyTree char_literal172_tree=null;
		DafnyTree LENGTH173_tree=null;
		DafnyTree char_literal174_tree=null;
		DafnyTree ID175_tree=null;
		DafnyTree char_literal176_tree=null;
		DafnyTree char_literal178_tree=null;
		DafnyTree char_literal179_tree=null;
		DafnyTree ID180_tree=null;
		RewriteRuleTokenStream stream_67=new RewriteRuleTokenStream(adaptor,"token 67");
		RewriteRuleTokenStream stream_68=new RewriteRuleTokenStream(adaptor,"token 68");
		RewriteRuleTokenStream stream_LENGTH=new RewriteRuleTokenStream(adaptor,"token LENGTH");
		RewriteRuleTokenStream stream_DOT=new RewriteRuleTokenStream(adaptor,"token DOT");
		RewriteRuleTokenStream stream_72=new RewriteRuleTokenStream(adaptor,"token 72");
		RewriteRuleTokenStream stream_ID=new RewriteRuleTokenStream(adaptor,"token ID");
		RewriteRuleTokenStream stream_73=new RewriteRuleTokenStream(adaptor,"token 73");
		RewriteRuleSubtreeStream stream_expression=new RewriteRuleSubtreeStream(adaptor,"rule expression");
		RewriteRuleSubtreeStream stream_atom_expr=new RewriteRuleSubtreeStream(adaptor,"rule atom_expr");
		RewriteRuleSubtreeStream stream_expressions=new RewriteRuleSubtreeStream(adaptor,"rule expressions");

		try {
			// src/edu/kit/iti/algover/parser/Dafny.g:263:13: ( ( atom_expr -> atom_expr ) ( '[' expression ']' -> ^( ARRAY_ACCESS atom_expr expression ) | '.' LENGTH -> ^( LENGTH atom_expr ) | '.' ID '(' expressions ')' -> ^( OBJ_FUNC_CALL ID atom_expr expressions ) | '.' ID -> ^( FIELD_ACCESS atom_expr ID ) )* )
			// src/edu/kit/iti/algover/parser/Dafny.g:264:3: ( atom_expr -> atom_expr ) ( '[' expression ']' -> ^( ARRAY_ACCESS atom_expr expression ) | '.' LENGTH -> ^( LENGTH atom_expr ) | '.' ID '(' expressions ')' -> ^( OBJ_FUNC_CALL ID atom_expr expressions ) | '.' ID -> ^( FIELD_ACCESS atom_expr ID ) )*
			{
			// src/edu/kit/iti/algover/parser/Dafny.g:264:3: ( atom_expr -> atom_expr )
			// src/edu/kit/iti/algover/parser/Dafny.g:264:5: atom_expr
			{
			pushFollow(FOLLOW_atom_expr_in_postfix_expr1753);
			atom_expr168=atom_expr();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) stream_atom_expr.add(atom_expr168.getTree());
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
			// 264:15: -> atom_expr
			{
				adaptor.addChild(root_0, stream_atom_expr.nextTree());
			}


			retval.tree = root_0;
			}

			}

			// src/edu/kit/iti/algover/parser/Dafny.g:265:3: ( '[' expression ']' -> ^( ARRAY_ACCESS atom_expr expression ) | '.' LENGTH -> ^( LENGTH atom_expr ) | '.' ID '(' expressions ')' -> ^( OBJ_FUNC_CALL ID atom_expr expressions ) | '.' ID -> ^( FIELD_ACCESS atom_expr ID ) )*
			loop40:
			while (true) {
				int alt40=5;
				int LA40_0 = input.LA(1);
				if ( (LA40_0==72) ) {
					alt40=1;
				}
				else if ( (LA40_0==DOT) ) {
					int LA40_3 = input.LA(2);
					if ( (LA40_3==LENGTH) ) {
						alt40=2;
					}
					else if ( (LA40_3==ID) ) {
						int LA40_5 = input.LA(3);
						if ( (LA40_5==67) ) {
							alt40=3;
						}
						else if ( (LA40_5==EOF||LA40_5==AND||LA40_5==ASSERT||LA40_5==ASSUME||(LA40_5 >= BLOCK_BEGIN && LA40_5 <= BLOCK_END)||(LA40_5 >= DECREASES && LA40_5 <= DOT)||(LA40_5 >= ENSURES && LA40_5 <= EQ)||(LA40_5 >= GE && LA40_5 <= GT)||(LA40_5 >= ID && LA40_5 <= IMPLIES)||(LA40_5 >= INTERSECT && LA40_5 <= LE)||LA40_5==LT||(LA40_5 >= MINUS && LA40_5 <= MODIFIES)||LA40_5==NEQ||(LA40_5 >= OR && LA40_5 <= REQUIRES)||(LA40_5 >= TIMES && LA40_5 <= WHILE)||(LA40_5 >= 68 && LA40_5 <= 69)||(LA40_5 >= 71 && LA40_5 <= 73)) ) {
							alt40=4;
						}

					}

				}

				switch (alt40) {
				case 1 :
					// src/edu/kit/iti/algover/parser/Dafny.g:265:5: '[' expression ']'
					{
					char_literal169=(Token)match(input,72,FOLLOW_72_in_postfix_expr1765); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_72.add(char_literal169);

					pushFollow(FOLLOW_expression_in_postfix_expr1767);
					expression170=expression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_expression.add(expression170.getTree());
					char_literal171=(Token)match(input,73,FOLLOW_73_in_postfix_expr1769); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_73.add(char_literal171);

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
					// 265:24: -> ^( ARRAY_ACCESS atom_expr expression )
					{
						// src/edu/kit/iti/algover/parser/Dafny.g:265:27: ^( ARRAY_ACCESS atom_expr expression )
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
					// src/edu/kit/iti/algover/parser/Dafny.g:266:5: '.' LENGTH
					{
					char_literal172=(Token)match(input,DOT,FOLLOW_DOT_in_postfix_expr1787); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_DOT.add(char_literal172);

					LENGTH173=(Token)match(input,LENGTH,FOLLOW_LENGTH_in_postfix_expr1789); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_LENGTH.add(LENGTH173);

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
					// 266:16: -> ^( LENGTH atom_expr )
					{
						// src/edu/kit/iti/algover/parser/Dafny.g:266:19: ^( LENGTH atom_expr )
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
					// src/edu/kit/iti/algover/parser/Dafny.g:267:5: '.' ID '(' expressions ')'
					{
					char_literal174=(Token)match(input,DOT,FOLLOW_DOT_in_postfix_expr1805); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_DOT.add(char_literal174);

					ID175=(Token)match(input,ID,FOLLOW_ID_in_postfix_expr1807); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_ID.add(ID175);

					char_literal176=(Token)match(input,67,FOLLOW_67_in_postfix_expr1809); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_67.add(char_literal176);

					pushFollow(FOLLOW_expressions_in_postfix_expr1811);
					expressions177=expressions();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_expressions.add(expressions177.getTree());
					char_literal178=(Token)match(input,68,FOLLOW_68_in_postfix_expr1813); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_68.add(char_literal178);

					// AST REWRITE
					// elements: atom_expr, ID, expressions
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (DafnyTree)adaptor.nil();
					// 267:32: -> ^( OBJ_FUNC_CALL ID atom_expr expressions )
					{
						// src/edu/kit/iti/algover/parser/Dafny.g:267:35: ^( OBJ_FUNC_CALL ID atom_expr expressions )
						{
						DafnyTree root_1 = (DafnyTree)adaptor.nil();
						root_1 = (DafnyTree)adaptor.becomeRoot((DafnyTree)adaptor.create(OBJ_FUNC_CALL, "OBJ_FUNC_CALL"), root_1);
						adaptor.addChild(root_1, stream_ID.nextNode());
						adaptor.addChild(root_1, stream_atom_expr.nextTree());
						adaptor.addChild(root_1, stream_expressions.nextTree());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;
				case 4 :
					// src/edu/kit/iti/algover/parser/Dafny.g:268:5: '.' ID
					{
					char_literal179=(Token)match(input,DOT,FOLLOW_DOT_in_postfix_expr1833); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_DOT.add(char_literal179);

					ID180=(Token)match(input,ID,FOLLOW_ID_in_postfix_expr1835); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_ID.add(ID180);

					// AST REWRITE
					// elements: atom_expr, ID
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (DafnyTree)adaptor.nil();
					// 268:12: -> ^( FIELD_ACCESS atom_expr ID )
					{
						// src/edu/kit/iti/algover/parser/Dafny.g:268:15: ^( FIELD_ACCESS atom_expr ID )
						{
						DafnyTree root_1 = (DafnyTree)adaptor.nil();
						root_1 = (DafnyTree)adaptor.becomeRoot((DafnyTree)adaptor.create(FIELD_ACCESS, "FIELD_ACCESS"), root_1);
						adaptor.addChild(root_1, stream_atom_expr.nextTree());
						adaptor.addChild(root_1, stream_ID.nextNode());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;

				default :
					break loop40;
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
	// $ANTLR end "postfix_expr"


	public static class expression_only_return extends ParserRuleReturnScope {
		DafnyTree tree;
		@Override
		public DafnyTree getTree() { return tree; }
	};


	// $ANTLR start "expression_only"
	// src/edu/kit/iti/algover/parser/Dafny.g:272:1: expression_only : expression EOF -> expression ;
	public final DafnyParser.expression_only_return expression_only() throws RecognitionException {
		DafnyParser.expression_only_return retval = new DafnyParser.expression_only_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		Token EOF182=null;
		ParserRuleReturnScope expression181 =null;

		DafnyTree EOF182_tree=null;
		RewriteRuleTokenStream stream_EOF=new RewriteRuleTokenStream(adaptor,"token EOF");
		RewriteRuleSubtreeStream stream_expression=new RewriteRuleSubtreeStream(adaptor,"rule expression");

		try {
			// src/edu/kit/iti/algover/parser/Dafny.g:272:16: ( expression EOF -> expression )
			// src/edu/kit/iti/algover/parser/Dafny.g:273:3: expression EOF
			{
			pushFollow(FOLLOW_expression_in_expression_only1864);
			expression181=expression();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) stream_expression.add(expression181.getTree());
			EOF182=(Token)match(input,EOF,FOLLOW_EOF_in_expression_only1866); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_EOF.add(EOF182);

			// AST REWRITE
			// elements: expression
			// token labels: 
			// rule labels: retval
			// token list labels: 
			// rule list labels: 
			// wildcard labels: 
			if ( state.backtracking==0 ) {
			retval.tree = root_0;
			RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

			root_0 = (DafnyTree)adaptor.nil();
			// 273:18: -> expression
			{
				adaptor.addChild(root_0, stream_expression.nextTree());
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
	// $ANTLR end "expression_only"


	public static class atom_expr_return extends ParserRuleReturnScope {
		DafnyTree tree;
		@Override
		public DafnyTree getTree() { return tree; }
	};


	// $ANTLR start "atom_expr"
	// src/edu/kit/iti/algover/parser/Dafny.g:277:1: atom_expr : ( ID | ID '(' expressions ')' -> ^( FUNC_CALL ID expressions ) | LIT | 'this' | NULL | quantifier | '(' ! expression ')' !|open= '{' ( expressions )? '}' -> ^( SETEX[$open] ( expressions )? ) |open= '[' ( expressions )? ']' -> ^( LISTEX[$open] ( expressions )? ) );
	public final DafnyParser.atom_expr_return atom_expr() throws RecognitionException {
		DafnyParser.atom_expr_return retval = new DafnyParser.atom_expr_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		Token open=null;
		Token ID183=null;
		Token ID184=null;
		Token char_literal185=null;
		Token char_literal187=null;
		Token LIT188=null;
		Token string_literal189=null;
		Token NULL190=null;
		Token char_literal192=null;
		Token char_literal194=null;
		Token char_literal196=null;
		Token char_literal198=null;
		ParserRuleReturnScope expressions186 =null;
		ParserRuleReturnScope quantifier191 =null;
		ParserRuleReturnScope expression193 =null;
		ParserRuleReturnScope expressions195 =null;
		ParserRuleReturnScope expressions197 =null;

		DafnyTree open_tree=null;
		DafnyTree ID183_tree=null;
		DafnyTree ID184_tree=null;
		DafnyTree char_literal185_tree=null;
		DafnyTree char_literal187_tree=null;
		DafnyTree LIT188_tree=null;
		DafnyTree string_literal189_tree=null;
		DafnyTree NULL190_tree=null;
		DafnyTree char_literal192_tree=null;
		DafnyTree char_literal194_tree=null;
		DafnyTree char_literal196_tree=null;
		DafnyTree char_literal198_tree=null;
		RewriteRuleTokenStream stream_67=new RewriteRuleTokenStream(adaptor,"token 67");
		RewriteRuleTokenStream stream_68=new RewriteRuleTokenStream(adaptor,"token 68");
		RewriteRuleTokenStream stream_BLOCK_END=new RewriteRuleTokenStream(adaptor,"token BLOCK_END");
		RewriteRuleTokenStream stream_BLOCK_BEGIN=new RewriteRuleTokenStream(adaptor,"token BLOCK_BEGIN");
		RewriteRuleTokenStream stream_ID=new RewriteRuleTokenStream(adaptor,"token ID");
		RewriteRuleTokenStream stream_72=new RewriteRuleTokenStream(adaptor,"token 72");
		RewriteRuleTokenStream stream_73=new RewriteRuleTokenStream(adaptor,"token 73");
		RewriteRuleSubtreeStream stream_expressions=new RewriteRuleSubtreeStream(adaptor,"rule expressions");

		try {
			// src/edu/kit/iti/algover/parser/Dafny.g:277:10: ( ID | ID '(' expressions ')' -> ^( FUNC_CALL ID expressions ) | LIT | 'this' | NULL | quantifier | '(' ! expression ')' !|open= '{' ( expressions )? '}' -> ^( SETEX[$open] ( expressions )? ) |open= '[' ( expressions )? ']' -> ^( LISTEX[$open] ( expressions )? ) )
			int alt43=9;
			switch ( input.LA(1) ) {
			case ID:
				{
				int LA43_1 = input.LA(2);
				if ( (LA43_1==67) ) {
					alt43=2;
				}
				else if ( (LA43_1==EOF||LA43_1==AND||LA43_1==ASSERT||LA43_1==ASSUME||(LA43_1 >= BLOCK_BEGIN && LA43_1 <= BLOCK_END)||(LA43_1 >= DECREASES && LA43_1 <= DOT)||(LA43_1 >= ENSURES && LA43_1 <= EQ)||(LA43_1 >= GE && LA43_1 <= GT)||(LA43_1 >= ID && LA43_1 <= IMPLIES)||(LA43_1 >= INTERSECT && LA43_1 <= LE)||LA43_1==LT||(LA43_1 >= MINUS && LA43_1 <= MODIFIES)||LA43_1==NEQ||(LA43_1 >= OR && LA43_1 <= REQUIRES)||(LA43_1 >= TIMES && LA43_1 <= WHILE)||(LA43_1 >= 68 && LA43_1 <= 69)||(LA43_1 >= 71 && LA43_1 <= 73)) ) {
					alt43=1;
				}

				else {
					if (state.backtracking>0) {state.failed=true; return retval;}
					int nvaeMark = input.mark();
					try {
						input.consume();
						NoViableAltException nvae =
							new NoViableAltException("", 43, 1, input);
						throw nvae;
					} finally {
						input.rewind(nvaeMark);
					}
				}

				}
				break;
			case LIT:
				{
				alt43=3;
				}
				break;
			case THIS:
				{
				alt43=4;
				}
				break;
			case NULL:
				{
				alt43=5;
				}
				break;
			case 67:
				{
				int LA43_5 = input.LA(2);
				if ( (LA43_5==ALL||LA43_5==EX) ) {
					alt43=6;
				}
				else if ( (LA43_5==BLOCK_BEGIN||LA43_5==ID||LA43_5==LIT||LA43_5==MINUS||(LA43_5 >= NOT && LA43_5 <= NULL)||LA43_5==THIS||LA43_5==67||LA43_5==72) ) {
					alt43=7;
				}

				else {
					if (state.backtracking>0) {state.failed=true; return retval;}
					int nvaeMark = input.mark();
					try {
						input.consume();
						NoViableAltException nvae =
							new NoViableAltException("", 43, 5, input);
						throw nvae;
					} finally {
						input.rewind(nvaeMark);
					}
				}

				}
				break;
			case BLOCK_BEGIN:
				{
				alt43=8;
				}
				break;
			case 72:
				{
				alt43=9;
				}
				break;
			default:
				if (state.backtracking>0) {state.failed=true; return retval;}
				NoViableAltException nvae =
					new NoViableAltException("", 43, 0, input);
				throw nvae;
			}
			switch (alt43) {
				case 1 :
					// src/edu/kit/iti/algover/parser/Dafny.g:278:5: ID
					{
					root_0 = (DafnyTree)adaptor.nil();


					ID183=(Token)match(input,ID,FOLLOW_ID_in_atom_expr1885); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					ID183_tree = (DafnyTree)adaptor.create(ID183);
					adaptor.addChild(root_0, ID183_tree);
					}

					}
					break;
				case 2 :
					// src/edu/kit/iti/algover/parser/Dafny.g:279:5: ID '(' expressions ')'
					{
					ID184=(Token)match(input,ID,FOLLOW_ID_in_atom_expr1891); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_ID.add(ID184);

					char_literal185=(Token)match(input,67,FOLLOW_67_in_atom_expr1893); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_67.add(char_literal185);

					pushFollow(FOLLOW_expressions_in_atom_expr1895);
					expressions186=expressions();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_expressions.add(expressions186.getTree());
					char_literal187=(Token)match(input,68,FOLLOW_68_in_atom_expr1897); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_68.add(char_literal187);

					// AST REWRITE
					// elements: expressions, ID
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (DafnyTree)adaptor.nil();
					// 279:28: -> ^( FUNC_CALL ID expressions )
					{
						// src/edu/kit/iti/algover/parser/Dafny.g:279:31: ^( FUNC_CALL ID expressions )
						{
						DafnyTree root_1 = (DafnyTree)adaptor.nil();
						root_1 = (DafnyTree)adaptor.becomeRoot((DafnyTree)adaptor.create(FUNC_CALL, "FUNC_CALL"), root_1);
						adaptor.addChild(root_1, stream_ID.nextNode());
						adaptor.addChild(root_1, stream_expressions.nextTree());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;
				case 3 :
					// src/edu/kit/iti/algover/parser/Dafny.g:280:5: LIT
					{
					root_0 = (DafnyTree)adaptor.nil();


					LIT188=(Token)match(input,LIT,FOLLOW_LIT_in_atom_expr1913); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					LIT188_tree = (DafnyTree)adaptor.create(LIT188);
					adaptor.addChild(root_0, LIT188_tree);
					}

					}
					break;
				case 4 :
					// src/edu/kit/iti/algover/parser/Dafny.g:281:5: 'this'
					{
					root_0 = (DafnyTree)adaptor.nil();


					string_literal189=(Token)match(input,THIS,FOLLOW_THIS_in_atom_expr1919); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					string_literal189_tree = (DafnyTree)adaptor.create(string_literal189);
					adaptor.addChild(root_0, string_literal189_tree);
					}

					}
					break;
				case 5 :
					// src/edu/kit/iti/algover/parser/Dafny.g:282:5: NULL
					{
					root_0 = (DafnyTree)adaptor.nil();


					NULL190=(Token)match(input,NULL,FOLLOW_NULL_in_atom_expr1925); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					NULL190_tree = (DafnyTree)adaptor.create(NULL190);
					adaptor.addChild(root_0, NULL190_tree);
					}

					}
					break;
				case 6 :
					// src/edu/kit/iti/algover/parser/Dafny.g:283:5: quantifier
					{
					root_0 = (DafnyTree)adaptor.nil();


					pushFollow(FOLLOW_quantifier_in_atom_expr1931);
					quantifier191=quantifier();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, quantifier191.getTree());

					}
					break;
				case 7 :
					// src/edu/kit/iti/algover/parser/Dafny.g:284:5: '(' ! expression ')' !
					{
					root_0 = (DafnyTree)adaptor.nil();


					char_literal192=(Token)match(input,67,FOLLOW_67_in_atom_expr1937); if (state.failed) return retval;
					pushFollow(FOLLOW_expression_in_atom_expr1940);
					expression193=expression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, expression193.getTree());

					char_literal194=(Token)match(input,68,FOLLOW_68_in_atom_expr1942); if (state.failed) return retval;
					}
					break;
				case 8 :
					// src/edu/kit/iti/algover/parser/Dafny.g:285:5: open= '{' ( expressions )? '}'
					{
					open=(Token)match(input,BLOCK_BEGIN,FOLLOW_BLOCK_BEGIN_in_atom_expr1951); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_BLOCK_BEGIN.add(open);

					// src/edu/kit/iti/algover/parser/Dafny.g:285:14: ( expressions )?
					int alt41=2;
					int LA41_0 = input.LA(1);
					if ( (LA41_0==BLOCK_BEGIN||LA41_0==ID||LA41_0==LIT||LA41_0==MINUS||(LA41_0 >= NOT && LA41_0 <= NULL)||LA41_0==THIS||LA41_0==67||LA41_0==72) ) {
						alt41=1;
					}
					switch (alt41) {
						case 1 :
							// src/edu/kit/iti/algover/parser/Dafny.g:285:14: expressions
							{
							pushFollow(FOLLOW_expressions_in_atom_expr1953);
							expressions195=expressions();
							state._fsp--;
							if (state.failed) return retval;
							if ( state.backtracking==0 ) stream_expressions.add(expressions195.getTree());
							}
							break;

					}

					char_literal196=(Token)match(input,BLOCK_END,FOLLOW_BLOCK_END_in_atom_expr1956); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_BLOCK_END.add(char_literal196);

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
					// 285:31: -> ^( SETEX[$open] ( expressions )? )
					{
						// src/edu/kit/iti/algover/parser/Dafny.g:285:34: ^( SETEX[$open] ( expressions )? )
						{
						DafnyTree root_1 = (DafnyTree)adaptor.nil();
						root_1 = (DafnyTree)adaptor.becomeRoot((DafnyTree)adaptor.create(SETEX, open), root_1);
						// src/edu/kit/iti/algover/parser/Dafny.g:285:49: ( expressions )?
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
				case 9 :
					// src/edu/kit/iti/algover/parser/Dafny.g:286:5: open= '[' ( expressions )? ']'
					{
					open=(Token)match(input,72,FOLLOW_72_in_atom_expr1974); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_72.add(open);

					// src/edu/kit/iti/algover/parser/Dafny.g:286:14: ( expressions )?
					int alt42=2;
					int LA42_0 = input.LA(1);
					if ( (LA42_0==BLOCK_BEGIN||LA42_0==ID||LA42_0==LIT||LA42_0==MINUS||(LA42_0 >= NOT && LA42_0 <= NULL)||LA42_0==THIS||LA42_0==67||LA42_0==72) ) {
						alt42=1;
					}
					switch (alt42) {
						case 1 :
							// src/edu/kit/iti/algover/parser/Dafny.g:286:14: expressions
							{
							pushFollow(FOLLOW_expressions_in_atom_expr1976);
							expressions197=expressions();
							state._fsp--;
							if (state.failed) return retval;
							if ( state.backtracking==0 ) stream_expressions.add(expressions197.getTree());
							}
							break;

					}

					char_literal198=(Token)match(input,73,FOLLOW_73_in_atom_expr1979); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_73.add(char_literal198);

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
					// 286:31: -> ^( LISTEX[$open] ( expressions )? )
					{
						// src/edu/kit/iti/algover/parser/Dafny.g:286:34: ^( LISTEX[$open] ( expressions )? )
						{
						DafnyTree root_1 = (DafnyTree)adaptor.nil();
						root_1 = (DafnyTree)adaptor.becomeRoot((DafnyTree)adaptor.create(LISTEX, open), root_1);
						// src/edu/kit/iti/algover/parser/Dafny.g:286:50: ( expressions )?
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
	// src/edu/kit/iti/algover/parser/Dafny.g:289:1: quantifier : '(' ! ( ALL ^| EX ^) ID ':' ! type '::' ! expression ')' !;
	public final DafnyParser.quantifier_return quantifier() throws RecognitionException {
		DafnyParser.quantifier_return retval = new DafnyParser.quantifier_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		Token char_literal199=null;
		Token ALL200=null;
		Token EX201=null;
		Token ID202=null;
		Token char_literal203=null;
		Token string_literal205=null;
		Token char_literal207=null;
		ParserRuleReturnScope type204 =null;
		ParserRuleReturnScope expression206 =null;

		DafnyTree char_literal199_tree=null;
		DafnyTree ALL200_tree=null;
		DafnyTree EX201_tree=null;
		DafnyTree ID202_tree=null;
		DafnyTree char_literal203_tree=null;
		DafnyTree string_literal205_tree=null;
		DafnyTree char_literal207_tree=null;

		try {
			// src/edu/kit/iti/algover/parser/Dafny.g:289:11: ( '(' ! ( ALL ^| EX ^) ID ':' ! type '::' ! expression ')' !)
			// src/edu/kit/iti/algover/parser/Dafny.g:290:3: '(' ! ( ALL ^| EX ^) ID ':' ! type '::' ! expression ')' !
			{
			root_0 = (DafnyTree)adaptor.nil();


			char_literal199=(Token)match(input,67,FOLLOW_67_in_quantifier2001); if (state.failed) return retval;
			// src/edu/kit/iti/algover/parser/Dafny.g:290:8: ( ALL ^| EX ^)
			int alt44=2;
			int LA44_0 = input.LA(1);
			if ( (LA44_0==ALL) ) {
				alt44=1;
			}
			else if ( (LA44_0==EX) ) {
				alt44=2;
			}

			else {
				if (state.backtracking>0) {state.failed=true; return retval;}
				NoViableAltException nvae =
					new NoViableAltException("", 44, 0, input);
				throw nvae;
			}

			switch (alt44) {
				case 1 :
					// src/edu/kit/iti/algover/parser/Dafny.g:290:9: ALL ^
					{
					ALL200=(Token)match(input,ALL,FOLLOW_ALL_in_quantifier2005); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					ALL200_tree = (DafnyTree)adaptor.create(ALL200);
					root_0 = (DafnyTree)adaptor.becomeRoot(ALL200_tree, root_0);
					}

					}
					break;
				case 2 :
					// src/edu/kit/iti/algover/parser/Dafny.g:290:16: EX ^
					{
					EX201=(Token)match(input,EX,FOLLOW_EX_in_quantifier2010); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					EX201_tree = (DafnyTree)adaptor.create(EX201);
					root_0 = (DafnyTree)adaptor.becomeRoot(EX201_tree, root_0);
					}

					}
					break;

			}

			ID202=(Token)match(input,ID,FOLLOW_ID_in_quantifier2014); if (state.failed) return retval;
			if ( state.backtracking==0 ) {
			ID202_tree = (DafnyTree)adaptor.create(ID202);
			adaptor.addChild(root_0, ID202_tree);
			}

			char_literal203=(Token)match(input,70,FOLLOW_70_in_quantifier2016); if (state.failed) return retval;
			pushFollow(FOLLOW_type_in_quantifier2019);
			type204=type();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, type204.getTree());

			string_literal205=(Token)match(input,DOUBLECOLON,FOLLOW_DOUBLECOLON_in_quantifier2021); if (state.failed) return retval;
			pushFollow(FOLLOW_expression_in_quantifier2024);
			expression206=expression();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, expression206.getTree());

			char_literal207=(Token)match(input,68,FOLLOW_68_in_quantifier2026); if (state.failed) return retval;
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
		// src/edu/kit/iti/algover/parser/Dafny.g:213:5: ( ID ':=' 'call' )
		// src/edu/kit/iti/algover/parser/Dafny.g:213:6: ID ':=' 'call'
		{
		match(input,ID,FOLLOW_ID_in_synpred1_Dafny1240); if (state.failed) return;

		match(input,ASSIGN,FOLLOW_ASSIGN_in_synpred1_Dafny1242); if (state.failed) return;

		match(input,CALL,FOLLOW_CALL_in_synpred1_Dafny1244); if (state.failed) return;

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



	public static final BitSet FOLLOW_LABEL_in_label590 = new BitSet(new long[]{0x0000000080000000L});
	public static final BitSet FOLLOW_ID_in_label593 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000040L});
	public static final BitSet FOLLOW_70_in_label595 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_method_in_program609 = new BitSet(new long[]{0x0000108004020002L});
	public static final BitSet FOLLOW_function_in_program613 = new BitSet(new long[]{0x0000108004020002L});
	public static final BitSet FOLLOW_clazz_in_program617 = new BitSet(new long[]{0x0000108004020002L});
	public static final BitSet FOLLOW_CLASS_in_clazz632 = new BitSet(new long[]{0x0000000080000000L});
	public static final BitSet FOLLOW_ID_in_clazz635 = new BitSet(new long[]{0x0000000000004000L});
	public static final BitSet FOLLOW_BLOCK_BEGIN_in_clazz637 = new BitSet(new long[]{0x0000108004000000L,0x0000000000000001L});
	public static final BitSet FOLLOW_method_in_clazz644 = new BitSet(new long[]{0x0000108004008000L,0x0000000000000001L});
	public static final BitSet FOLLOW_function_in_clazz648 = new BitSet(new long[]{0x0000108004008000L,0x0000000000000001L});
	public static final BitSet FOLLOW_field_in_clazz652 = new BitSet(new long[]{0x0000108004008000L,0x0000000000000001L});
	public static final BitSet FOLLOW_BLOCK_END_in_clazz658 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_METHOD_in_method676 = new BitSet(new long[]{0x0000000080000000L});
	public static final BitSet FOLLOW_LEMMA_in_method680 = new BitSet(new long[]{0x0000000080000000L});
	public static final BitSet FOLLOW_ID_in_method685 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000008L});
	public static final BitSet FOLLOW_67_in_method687 = new BitSet(new long[]{0x0000000080000000L,0x0000000000000010L});
	public static final BitSet FOLLOW_vars_in_method689 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000010L});
	public static final BitSet FOLLOW_68_in_method692 = new BitSet(new long[]{0x0140000000444000L});
	public static final BitSet FOLLOW_returns__in_method698 = new BitSet(new long[]{0x0040000000444000L});
	public static final BitSet FOLLOW_requires_in_method707 = new BitSet(new long[]{0x0040000000444000L});
	public static final BitSet FOLLOW_ensures_in_method716 = new BitSet(new long[]{0x0000000000444000L});
	public static final BitSet FOLLOW_decreases_in_method725 = new BitSet(new long[]{0x0000000000004000L});
	public static final BitSet FOLLOW_BLOCK_BEGIN_in_method732 = new BitSet(new long[]{0x0000002180009400L,0x0000000000000003L});
	public static final BitSet FOLLOW_statements_in_method734 = new BitSet(new long[]{0x0000000000008000L});
	public static final BitSet FOLLOW_BLOCK_END_in_method737 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_FUNCTION_in_function799 = new BitSet(new long[]{0x0000000080000000L});
	public static final BitSet FOLLOW_ID_in_function804 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000008L});
	public static final BitSet FOLLOW_67_in_function806 = new BitSet(new long[]{0x0000000080000000L,0x0000000000000010L});
	public static final BitSet FOLLOW_vars_in_function809 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000010L});
	public static final BitSet FOLLOW_68_in_function812 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000040L});
	public static final BitSet FOLLOW_70_in_function815 = new BitSet(new long[]{0x0200000400000080L});
	public static final BitSet FOLLOW_type_in_function818 = new BitSet(new long[]{0x0000000000004000L});
	public static final BitSet FOLLOW_BLOCK_BEGIN_in_function822 = new BitSet(new long[]{0x2006240080004000L,0x0000000000000108L});
	public static final BitSet FOLLOW_expression_in_function825 = new BitSet(new long[]{0x0000000000008000L});
	public static final BitSet FOLLOW_BLOCK_END_in_function827 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_VAR_in_field840 = new BitSet(new long[]{0x0000000080000000L});
	public static final BitSet FOLLOW_ID_in_field842 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000040L});
	public static final BitSet FOLLOW_70_in_field844 = new BitSet(new long[]{0x0200000400000080L});
	public static final BitSet FOLLOW_type_in_field846 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000080L});
	public static final BitSet FOLLOW_71_in_field848 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_var_in_vars860 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000020L});
	public static final BitSet FOLLOW_69_in_vars866 = new BitSet(new long[]{0x0000000080000000L});
	public static final BitSet FOLLOW_var_in_vars869 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000020L});
	public static final BitSet FOLLOW_ID_in_var884 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000040L});
	public static final BitSet FOLLOW_70_in_var886 = new BitSet(new long[]{0x0200000400000080L});
	public static final BitSet FOLLOW_type_in_var888 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_INT_in_type912 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_SET_in_type916 = new BitSet(new long[]{0x0000080000000000L});
	public static final BitSet FOLLOW_LT_in_type919 = new BitSet(new long[]{0x0000000400000000L});
	public static final BitSet FOLLOW_INT_in_type922 = new BitSet(new long[]{0x0000000020000000L});
	public static final BitSet FOLLOW_GT_in_type924 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_ARRAY_in_type931 = new BitSet(new long[]{0x0000080000000000L});
	public static final BitSet FOLLOW_LT_in_type934 = new BitSet(new long[]{0x0000000400000000L});
	public static final BitSet FOLLOW_INT_in_type937 = new BitSet(new long[]{0x0000000020000000L});
	public static final BitSet FOLLOW_GT_in_type939 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_RETURNS_in_returns_952 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000008L});
	public static final BitSet FOLLOW_67_in_returns_955 = new BitSet(new long[]{0x0000000080000000L});
	public static final BitSet FOLLOW_vars_in_returns_958 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000010L});
	public static final BitSet FOLLOW_68_in_returns_960 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_REQUIRES_in_requires973 = new BitSet(new long[]{0x2006242080004000L,0x0000000000000108L});
	public static final BitSet FOLLOW_label_in_requires976 = new BitSet(new long[]{0x2006240080004000L,0x0000000000000108L});
	public static final BitSet FOLLOW_expression_in_requires979 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_ENSURES_in_ensures991 = new BitSet(new long[]{0x2006242080004000L,0x0000000000000108L});
	public static final BitSet FOLLOW_label_in_ensures994 = new BitSet(new long[]{0x2006240080004000L,0x0000000000000108L});
	public static final BitSet FOLLOW_expression_in_ensures997 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_DECREASES_in_decreases1009 = new BitSet(new long[]{0x2006240080004000L,0x0000000000000108L});
	public static final BitSet FOLLOW_expression_in_decreases1012 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_INVARIANT_in_invariant1024 = new BitSet(new long[]{0x2006242080004000L,0x0000000000000108L});
	public static final BitSet FOLLOW_label_in_invariant1027 = new BitSet(new long[]{0x2006240080004000L,0x0000000000000108L});
	public static final BitSet FOLLOW_expression_in_invariant1030 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_MODIFIES_in_modifies1042 = new BitSet(new long[]{0x2006240080004000L,0x0000000000000108L});
	public static final BitSet FOLLOW_expressions_in_modifies1045 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_BLOCK_BEGIN_in_block1057 = new BitSet(new long[]{0x0000002180009400L,0x0000000000000003L});
	public static final BitSet FOLLOW_statements_in_block1059 = new BitSet(new long[]{0x0000000000008000L});
	public static final BitSet FOLLOW_BLOCK_END_in_block1062 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_block_in_relaxedBlock1085 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_statement_in_relaxedBlock1091 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_statement_in_statements1113 = new BitSet(new long[]{0x0000002180001402L,0x0000000000000003L});
	public static final BitSet FOLLOW_VAR_in_statement1130 = new BitSet(new long[]{0x0000000080000000L});
	public static final BitSet FOLLOW_ID_in_statement1133 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000040L});
	public static final BitSet FOLLOW_70_in_statement1135 = new BitSet(new long[]{0x0200000400000080L});
	public static final BitSet FOLLOW_type_in_statement1138 = new BitSet(new long[]{0x0000000000000800L,0x0000000000000080L});
	public static final BitSet FOLLOW_ASSIGN_in_statement1141 = new BitSet(new long[]{0x2006240080004000L,0x0000000000000108L});
	public static final BitSet FOLLOW_expression_in_statement1144 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000080L});
	public static final BitSet FOLLOW_71_in_statement1148 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_ID_in_statement1155 = new BitSet(new long[]{0x0000000000000800L});
	public static final BitSet FOLLOW_ASSIGN_in_statement1159 = new BitSet(new long[]{0x4000000000000000L});
	public static final BitSet FOLLOW_TIMES_in_statement1161 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000080L});
	public static final BitSet FOLLOW_71_in_statement1163 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_ID_in_statement1178 = new BitSet(new long[]{0x0000000000000800L});
	public static final BitSet FOLLOW_ASSIGN_in_statement1180 = new BitSet(new long[]{0x2006240080004000L,0x0000000000000108L});
	public static final BitSet FOLLOW_expression_in_statement1183 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000080L});
	public static final BitSet FOLLOW_71_in_statement1185 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_ID_in_statement1192 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000100L});
	public static final BitSet FOLLOW_72_in_statement1194 = new BitSet(new long[]{0x2006240080004000L,0x0000000000000108L});
	public static final BitSet FOLLOW_expression_in_statement1198 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000200L});
	public static final BitSet FOLLOW_73_in_statement1200 = new BitSet(new long[]{0x0000000000000800L});
	public static final BitSet FOLLOW_ASSIGN_in_statement1204 = new BitSet(new long[]{0x2006240080004000L,0x0000000000000108L});
	public static final BitSet FOLLOW_expression_in_statement1208 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000080L});
	public static final BitSet FOLLOW_71_in_statement1210 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_ID_in_statement1251 = new BitSet(new long[]{0x0000000000000800L});
	public static final BitSet FOLLOW_ASSIGN_in_statement1253 = new BitSet(new long[]{0x0000000000010000L});
	public static final BitSet FOLLOW_CALL_in_statement1255 = new BitSet(new long[]{0x0000000080000000L});
	public static final BitSet FOLLOW_ID_in_statement1259 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000008L});
	public static final BitSet FOLLOW_67_in_statement1261 = new BitSet(new long[]{0x2006240080004000L,0x0000000000000118L});
	public static final BitSet FOLLOW_expressions_in_statement1263 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000010L});
	public static final BitSet FOLLOW_68_in_statement1266 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000080L});
	public static final BitSet FOLLOW_71_in_statement1268 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_ids_in_statement1305 = new BitSet(new long[]{0x0000000000000800L});
	public static final BitSet FOLLOW_ASSIGN_in_statement1307 = new BitSet(new long[]{0x0000000000010000L});
	public static final BitSet FOLLOW_CALL_in_statement1309 = new BitSet(new long[]{0x0000000080000000L});
	public static final BitSet FOLLOW_ID_in_statement1311 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000008L});
	public static final BitSet FOLLOW_67_in_statement1313 = new BitSet(new long[]{0x2006240080004000L,0x0000000000000118L});
	public static final BitSet FOLLOW_expressions_in_statement1315 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000010L});
	public static final BitSet FOLLOW_68_in_statement1318 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000080L});
	public static final BitSet FOLLOW_71_in_statement1320 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_label_in_statement1355 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000002L});
	public static final BitSet FOLLOW_WHILE_in_statement1364 = new BitSet(new long[]{0x2006240080004000L,0x0000000000000108L});
	public static final BitSet FOLLOW_expression_in_statement1366 = new BitSet(new long[]{0x0000001000000000L});
	public static final BitSet FOLLOW_invariant_in_statement1368 = new BitSet(new long[]{0x0000401000040000L});
	public static final BitSet FOLLOW_modifies_in_statement1371 = new BitSet(new long[]{0x0000000000040000L});
	public static final BitSet FOLLOW_decreases_in_statement1374 = new BitSet(new long[]{0x0000002180005400L,0x0000000000000003L});
	public static final BitSet FOLLOW_relaxedBlock_in_statement1376 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_label_in_statement1411 = new BitSet(new long[]{0x0000000100000000L});
	public static final BitSet FOLLOW_IF_in_statement1414 = new BitSet(new long[]{0x2006240080004000L,0x0000000000000108L});
	public static final BitSet FOLLOW_expression_in_statement1417 = new BitSet(new long[]{0x0000002180005400L,0x0000000000000003L});
	public static final BitSet FOLLOW_relaxedBlock_in_statement1419 = new BitSet(new long[]{0x0000000000200002L});
	public static final BitSet FOLLOW_ELSE_in_statement1440 = new BitSet(new long[]{0x0000002180005400L,0x0000000000000003L});
	public static final BitSet FOLLOW_relaxedBlock_in_statement1443 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_ASSERT_in_statement1452 = new BitSet(new long[]{0x2006242080004000L,0x0000000000000108L});
	public static final BitSet FOLLOW_LABEL_in_statement1457 = new BitSet(new long[]{0x0000000080000000L});
	public static final BitSet FOLLOW_ID_in_statement1460 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000040L});
	public static final BitSet FOLLOW_70_in_statement1462 = new BitSet(new long[]{0x2006240080004000L,0x0000000000000108L});
	public static final BitSet FOLLOW_expression_in_statement1468 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000080L});
	public static final BitSet FOLLOW_71_in_statement1470 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_ASSUME_in_statement1477 = new BitSet(new long[]{0x2006242080004000L,0x0000000000000108L});
	public static final BitSet FOLLOW_LABEL_in_statement1482 = new BitSet(new long[]{0x0000000080000000L});
	public static final BitSet FOLLOW_ID_in_statement1485 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000040L});
	public static final BitSet FOLLOW_70_in_statement1487 = new BitSet(new long[]{0x2006240080004000L,0x0000000000000108L});
	public static final BitSet FOLLOW_expression_in_statement1493 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000080L});
	public static final BitSet FOLLOW_71_in_statement1495 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_ID_in_ids1508 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000020L});
	public static final BitSet FOLLOW_69_in_ids1511 = new BitSet(new long[]{0x0000000080000000L});
	public static final BitSet FOLLOW_ID_in_ids1514 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000020L});
	public static final BitSet FOLLOW_expression_in_expressions1528 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000020L});
	public static final BitSet FOLLOW_69_in_expressions1532 = new BitSet(new long[]{0x2006240080004000L,0x0000000000000108L});
	public static final BitSet FOLLOW_expression_in_expressions1535 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000020L});
	public static final BitSet FOLLOW_or_expr_in_expression1550 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_and_expr_in_or_expr1559 = new BitSet(new long[]{0x0010000200000002L});
	public static final BitSet FOLLOW_OR_in_or_expr1564 = new BitSet(new long[]{0x2006240080004000L,0x0000000000000108L});
	public static final BitSet FOLLOW_IMPLIES_in_or_expr1569 = new BitSet(new long[]{0x2006240080004000L,0x0000000000000108L});
	public static final BitSet FOLLOW_or_expr_in_or_expr1573 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_rel_expr_in_and_expr1588 = new BitSet(new long[]{0x0000000000000022L});
	public static final BitSet FOLLOW_AND_in_and_expr1592 = new BitSet(new long[]{0x2006240080004000L,0x0000000000000108L});
	public static final BitSet FOLLOW_and_expr_in_and_expr1595 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_add_expr_in_rel_expr1610 = new BitSet(new long[]{0x0001084030800002L});
	public static final BitSet FOLLOW_LT_in_rel_expr1615 = new BitSet(new long[]{0x2006240080004000L,0x0000000000000108L});
	public static final BitSet FOLLOW_GT_in_rel_expr1620 = new BitSet(new long[]{0x2006240080004000L,0x0000000000000108L});
	public static final BitSet FOLLOW_EQ_in_rel_expr1625 = new BitSet(new long[]{0x2006240080004000L,0x0000000000000108L});
	public static final BitSet FOLLOW_NEQ_in_rel_expr1630 = new BitSet(new long[]{0x2006240080004000L,0x0000000000000108L});
	public static final BitSet FOLLOW_LE_in_rel_expr1635 = new BitSet(new long[]{0x2006240080004000L,0x0000000000000108L});
	public static final BitSet FOLLOW_GE_in_rel_expr1640 = new BitSet(new long[]{0x2006240080004000L,0x0000000000000108L});
	public static final BitSet FOLLOW_add_expr_in_rel_expr1644 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_mul_expr_in_add_expr1659 = new BitSet(new long[]{0x8020200000000002L});
	public static final BitSet FOLLOW_set_in_add_expr1663 = new BitSet(new long[]{0x2006240080004000L,0x0000000000000108L});
	public static final BitSet FOLLOW_add_expr_in_add_expr1676 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_prefix_expr_in_mul_expr1691 = new BitSet(new long[]{0x4000000800000002L});
	public static final BitSet FOLLOW_set_in_mul_expr1695 = new BitSet(new long[]{0x2006240080004000L,0x0000000000000108L});
	public static final BitSet FOLLOW_mul_expr_in_mul_expr1704 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_MINUS_in_prefix_expr1721 = new BitSet(new long[]{0x2006240080004000L,0x0000000000000108L});
	public static final BitSet FOLLOW_prefix_expr_in_prefix_expr1724 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_NOT_in_prefix_expr1730 = new BitSet(new long[]{0x2006240080004000L,0x0000000000000108L});
	public static final BitSet FOLLOW_prefix_expr_in_prefix_expr1733 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_postfix_expr_in_prefix_expr1739 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_atom_expr_in_postfix_expr1753 = new BitSet(new long[]{0x0000000000080002L,0x0000000000000100L});
	public static final BitSet FOLLOW_72_in_postfix_expr1765 = new BitSet(new long[]{0x2006240080004000L,0x0000000000000108L});
	public static final BitSet FOLLOW_expression_in_postfix_expr1767 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000200L});
	public static final BitSet FOLLOW_73_in_postfix_expr1769 = new BitSet(new long[]{0x0000000000080002L,0x0000000000000100L});
	public static final BitSet FOLLOW_DOT_in_postfix_expr1787 = new BitSet(new long[]{0x0000010000000000L});
	public static final BitSet FOLLOW_LENGTH_in_postfix_expr1789 = new BitSet(new long[]{0x0000000000080002L,0x0000000000000100L});
	public static final BitSet FOLLOW_DOT_in_postfix_expr1805 = new BitSet(new long[]{0x0000000080000000L});
	public static final BitSet FOLLOW_ID_in_postfix_expr1807 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000008L});
	public static final BitSet FOLLOW_67_in_postfix_expr1809 = new BitSet(new long[]{0x2006240080004000L,0x0000000000000108L});
	public static final BitSet FOLLOW_expressions_in_postfix_expr1811 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000010L});
	public static final BitSet FOLLOW_68_in_postfix_expr1813 = new BitSet(new long[]{0x0000000000080002L,0x0000000000000100L});
	public static final BitSet FOLLOW_DOT_in_postfix_expr1833 = new BitSet(new long[]{0x0000000080000000L});
	public static final BitSet FOLLOW_ID_in_postfix_expr1835 = new BitSet(new long[]{0x0000000000080002L,0x0000000000000100L});
	public static final BitSet FOLLOW_expression_in_expression_only1864 = new BitSet(new long[]{0x0000000000000000L});
	public static final BitSet FOLLOW_EOF_in_expression_only1866 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_ID_in_atom_expr1885 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_ID_in_atom_expr1891 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000008L});
	public static final BitSet FOLLOW_67_in_atom_expr1893 = new BitSet(new long[]{0x2006240080004000L,0x0000000000000108L});
	public static final BitSet FOLLOW_expressions_in_atom_expr1895 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000010L});
	public static final BitSet FOLLOW_68_in_atom_expr1897 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_LIT_in_atom_expr1913 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_THIS_in_atom_expr1919 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_NULL_in_atom_expr1925 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_quantifier_in_atom_expr1931 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_67_in_atom_expr1937 = new BitSet(new long[]{0x2006240080004000L,0x0000000000000108L});
	public static final BitSet FOLLOW_expression_in_atom_expr1940 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000010L});
	public static final BitSet FOLLOW_68_in_atom_expr1942 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_BLOCK_BEGIN_in_atom_expr1951 = new BitSet(new long[]{0x200624008000C000L,0x0000000000000108L});
	public static final BitSet FOLLOW_expressions_in_atom_expr1953 = new BitSet(new long[]{0x0000000000008000L});
	public static final BitSet FOLLOW_BLOCK_END_in_atom_expr1956 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_72_in_atom_expr1974 = new BitSet(new long[]{0x2006240080004000L,0x0000000000000308L});
	public static final BitSet FOLLOW_expressions_in_atom_expr1976 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000200L});
	public static final BitSet FOLLOW_73_in_atom_expr1979 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_67_in_quantifier2001 = new BitSet(new long[]{0x0000000001000010L});
	public static final BitSet FOLLOW_ALL_in_quantifier2005 = new BitSet(new long[]{0x0000000080000000L});
	public static final BitSet FOLLOW_EX_in_quantifier2010 = new BitSet(new long[]{0x0000000080000000L});
	public static final BitSet FOLLOW_ID_in_quantifier2014 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000040L});
	public static final BitSet FOLLOW_70_in_quantifier2016 = new BitSet(new long[]{0x0200000400000080L});
	public static final BitSet FOLLOW_type_in_quantifier2019 = new BitSet(new long[]{0x0000000000100000L});
	public static final BitSet FOLLOW_DOUBLECOLON_in_quantifier2021 = new BitSet(new long[]{0x2006240080004000L,0x0000000000000108L});
	public static final BitSet FOLLOW_expression_in_quantifier2024 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000010L});
	public static final BitSet FOLLOW_68_in_quantifier2026 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_ID_in_synpred1_Dafny1240 = new BitSet(new long[]{0x0000000000000800L});
	public static final BitSet FOLLOW_ASSIGN_in_synpred1_Dafny1242 = new BitSet(new long[]{0x0000000000010000L});
	public static final BitSet FOLLOW_CALL_in_synpred1_Dafny1244 = new BitSet(new long[]{0x0000000000000002L});
}
