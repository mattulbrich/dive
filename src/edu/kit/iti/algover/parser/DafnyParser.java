// $ANTLR 3.5.1 src/edu/kit/iti/algover/parser/Dafny.g 2016-06-17 19:22:10

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
		"BLOCK_BEGIN", "BLOCK_END", "BOOL", "CALL", "CLASS", "DECREASES", "DOT", 
		"DOUBLECOLON", "ELSE", "ENSURES", "EQ", "EX", "FIELD_ACCESS", "FUNCTION", 
		"FUNC_CALL", "GE", "GT", "HAVOC", "ID", "IF", "IMPLIES", "INT", "INTERSECT", 
		"INVARIANT", "LABEL", "LE", "LEMMA", "LENGTH", "LISTEX", "LIT", "LT", 
		"METHOD", "MINUS", "MODIFIES", "MULTILINE_COMMENT", "NEQ", "NOT", "NULL", 
		"OBJ_FUNC_CALL", "OR", "PLUS", "REQUIRES", "RESULTS", "RETURNS", "SET", 
		"SETEX", "SINGLELINE_COMMENT", "THEN", "THIS", "TIMES", "UNION", "VAR", 
		"WHILE", "WS", "'('", "')'", "','", "':'", "';'", "'['", "']'"
	};
	public static final int EOF=-1;
	public static final int T__68=68;
	public static final int T__69=69;
	public static final int T__70=70;
	public static final int T__71=71;
	public static final int T__72=72;
	public static final int T__73=73;
	public static final int T__74=74;
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
	public static final int BOOL=16;
	public static final int CALL=17;
	public static final int CLASS=18;
	public static final int DECREASES=19;
	public static final int DOT=20;
	public static final int DOUBLECOLON=21;
	public static final int ELSE=22;
	public static final int ENSURES=23;
	public static final int EQ=24;
	public static final int EX=25;
	public static final int FIELD_ACCESS=26;
	public static final int FUNCTION=27;
	public static final int FUNC_CALL=28;
	public static final int GE=29;
	public static final int GT=30;
	public static final int HAVOC=31;
	public static final int ID=32;
	public static final int IF=33;
	public static final int IMPLIES=34;
	public static final int INT=35;
	public static final int INTERSECT=36;
	public static final int INVARIANT=37;
	public static final int LABEL=38;
	public static final int LE=39;
	public static final int LEMMA=40;
	public static final int LENGTH=41;
	public static final int LISTEX=42;
	public static final int LIT=43;
	public static final int LT=44;
	public static final int METHOD=45;
	public static final int MINUS=46;
	public static final int MODIFIES=47;
	public static final int MULTILINE_COMMENT=48;
	public static final int NEQ=49;
	public static final int NOT=50;
	public static final int NULL=51;
	public static final int OBJ_FUNC_CALL=52;
	public static final int OR=53;
	public static final int PLUS=54;
	public static final int REQUIRES=55;
	public static final int RESULTS=56;
	public static final int RETURNS=57;
	public static final int SET=58;
	public static final int SETEX=59;
	public static final int SINGLELINE_COMMENT=60;
	public static final int THEN=61;
	public static final int THIS=62;
	public static final int TIMES=63;
	public static final int UNION=64;
	public static final int VAR=65;
	public static final int WHILE=66;
	public static final int WS=67;

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
	// src/edu/kit/iti/algover/parser/Dafny.g:119:1: label : 'label' ^ ID ':' !;
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
			// src/edu/kit/iti/algover/parser/Dafny.g:119:6: ( 'label' ^ ID ':' !)
			// src/edu/kit/iti/algover/parser/Dafny.g:120:3: 'label' ^ ID ':' !
			{
			root_0 = (DafnyTree)adaptor.nil();


			string_literal1=(Token)match(input,LABEL,FOLLOW_LABEL_in_label597); if (state.failed) return retval;
			if ( state.backtracking==0 ) {
			string_literal1_tree = (DafnyTree)adaptor.create(string_literal1);
			root_0 = (DafnyTree)adaptor.becomeRoot(string_literal1_tree, root_0);
			}

			ID2=(Token)match(input,ID,FOLLOW_ID_in_label600); if (state.failed) return retval;
			if ( state.backtracking==0 ) {
			ID2_tree = (DafnyTree)adaptor.create(ID2);
			adaptor.addChild(root_0, ID2_tree);
			}

			char_literal3=(Token)match(input,71,FOLLOW_71_in_label602); if (state.failed) return retval;
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
	// src/edu/kit/iti/algover/parser/Dafny.g:123:1: program : ( method | function | clazz )+ ;
	public final DafnyParser.program_return program() throws RecognitionException {
		DafnyParser.program_return retval = new DafnyParser.program_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		ParserRuleReturnScope method4 =null;
		ParserRuleReturnScope function5 =null;
		ParserRuleReturnScope clazz6 =null;


		try {
			// src/edu/kit/iti/algover/parser/Dafny.g:123:8: ( ( method | function | clazz )+ )
			// src/edu/kit/iti/algover/parser/Dafny.g:124:3: ( method | function | clazz )+
			{
			root_0 = (DafnyTree)adaptor.nil();


			// src/edu/kit/iti/algover/parser/Dafny.g:124:3: ( method | function | clazz )+
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
					// src/edu/kit/iti/algover/parser/Dafny.g:124:4: method
					{
					pushFollow(FOLLOW_method_in_program616);
					method4=method();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, method4.getTree());

					}
					break;
				case 2 :
					// src/edu/kit/iti/algover/parser/Dafny.g:124:13: function
					{
					pushFollow(FOLLOW_function_in_program620);
					function5=function();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, function5.getTree());

					}
					break;
				case 3 :
					// src/edu/kit/iti/algover/parser/Dafny.g:124:24: clazz
					{
					pushFollow(FOLLOW_clazz_in_program624);
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
	// src/edu/kit/iti/algover/parser/Dafny.g:128:1: clazz : CLASS ^ ID '{' ( method | function | field )+ '}' ;
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
			// src/edu/kit/iti/algover/parser/Dafny.g:128:6: ( CLASS ^ ID '{' ( method | function | field )+ '}' )
			// src/edu/kit/iti/algover/parser/Dafny.g:129:3: CLASS ^ ID '{' ( method | function | field )+ '}'
			{
			root_0 = (DafnyTree)adaptor.nil();


			CLASS7=(Token)match(input,CLASS,FOLLOW_CLASS_in_clazz639); if (state.failed) return retval;
			if ( state.backtracking==0 ) {
			CLASS7_tree = (DafnyTree)adaptor.create(CLASS7);
			root_0 = (DafnyTree)adaptor.becomeRoot(CLASS7_tree, root_0);
			}

			ID8=(Token)match(input,ID,FOLLOW_ID_in_clazz642); if (state.failed) return retval;
			if ( state.backtracking==0 ) {
			ID8_tree = (DafnyTree)adaptor.create(ID8);
			adaptor.addChild(root_0, ID8_tree);
			}

			char_literal9=(Token)match(input,BLOCK_BEGIN,FOLLOW_BLOCK_BEGIN_in_clazz644); if (state.failed) return retval;
			if ( state.backtracking==0 ) {
			char_literal9_tree = (DafnyTree)adaptor.create(char_literal9);
			adaptor.addChild(root_0, char_literal9_tree);
			}

			// src/edu/kit/iti/algover/parser/Dafny.g:130:5: ( method | function | field )+
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
					// src/edu/kit/iti/algover/parser/Dafny.g:130:6: method
					{
					pushFollow(FOLLOW_method_in_clazz651);
					method10=method();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, method10.getTree());

					}
					break;
				case 2 :
					// src/edu/kit/iti/algover/parser/Dafny.g:130:15: function
					{
					pushFollow(FOLLOW_function_in_clazz655);
					function11=function();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, function11.getTree());

					}
					break;
				case 3 :
					// src/edu/kit/iti/algover/parser/Dafny.g:130:26: field
					{
					pushFollow(FOLLOW_field_in_clazz659);
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

			char_literal13=(Token)match(input,BLOCK_END,FOLLOW_BLOCK_END_in_clazz665); if (state.failed) return retval;
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
	// src/edu/kit/iti/algover/parser/Dafny.g:134:1: method : tok= ( 'method' | 'lemma' ) ID '(' ( vars )? ')' ( returns_ )? ( requires )* ( ensures )* ( decreases )? '{' ( statements )? '}' -> ^( METHOD[tok] ID ^( ARGS ( vars )? ) ( returns_ )? ( requires )* ( ensures )* ( decreases )? ^( BLOCK ( statements )? ) ) ;
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
		RewriteRuleTokenStream stream_68=new RewriteRuleTokenStream(adaptor,"token 68");
		RewriteRuleTokenStream stream_69=new RewriteRuleTokenStream(adaptor,"token 69");
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
			// src/edu/kit/iti/algover/parser/Dafny.g:134:7: (tok= ( 'method' | 'lemma' ) ID '(' ( vars )? ')' ( returns_ )? ( requires )* ( ensures )* ( decreases )? '{' ( statements )? '}' -> ^( METHOD[tok] ID ^( ARGS ( vars )? ) ( returns_ )? ( requires )* ( ensures )* ( decreases )? ^( BLOCK ( statements )? ) ) )
			// src/edu/kit/iti/algover/parser/Dafny.g:135:3: tok= ( 'method' | 'lemma' ) ID '(' ( vars )? ')' ( returns_ )? ( requires )* ( ensures )* ( decreases )? '{' ( statements )? '}'
			{
			// src/edu/kit/iti/algover/parser/Dafny.g:135:9: ( 'method' | 'lemma' )
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
					// src/edu/kit/iti/algover/parser/Dafny.g:135:10: 'method'
					{
					tok=(Token)match(input,METHOD,FOLLOW_METHOD_in_method683); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_METHOD.add(tok);

					}
					break;
				case 2 :
					// src/edu/kit/iti/algover/parser/Dafny.g:135:21: 'lemma'
					{
					tok=(Token)match(input,LEMMA,FOLLOW_LEMMA_in_method687); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_LEMMA.add(tok);

					}
					break;

			}

			ID14=(Token)match(input,ID,FOLLOW_ID_in_method692); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_ID.add(ID14);

			char_literal15=(Token)match(input,68,FOLLOW_68_in_method694); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_68.add(char_literal15);

			// src/edu/kit/iti/algover/parser/Dafny.g:136:10: ( vars )?
			int alt4=2;
			int LA4_0 = input.LA(1);
			if ( (LA4_0==ID) ) {
				alt4=1;
			}
			switch (alt4) {
				case 1 :
					// src/edu/kit/iti/algover/parser/Dafny.g:136:10: vars
					{
					pushFollow(FOLLOW_vars_in_method696);
					vars16=vars();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_vars.add(vars16.getTree());
					}
					break;

			}

			char_literal17=(Token)match(input,69,FOLLOW_69_in_method699); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_69.add(char_literal17);

			// src/edu/kit/iti/algover/parser/Dafny.g:137:3: ( returns_ )?
			int alt5=2;
			int LA5_0 = input.LA(1);
			if ( (LA5_0==RETURNS) ) {
				alt5=1;
			}
			switch (alt5) {
				case 1 :
					// src/edu/kit/iti/algover/parser/Dafny.g:137:5: returns_
					{
					pushFollow(FOLLOW_returns__in_method705);
					returns_18=returns_();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_returns_.add(returns_18.getTree());
					}
					break;

			}

			// src/edu/kit/iti/algover/parser/Dafny.g:138:3: ( requires )*
			loop6:
			while (true) {
				int alt6=2;
				int LA6_0 = input.LA(1);
				if ( (LA6_0==REQUIRES) ) {
					alt6=1;
				}

				switch (alt6) {
				case 1 :
					// src/edu/kit/iti/algover/parser/Dafny.g:138:5: requires
					{
					pushFollow(FOLLOW_requires_in_method714);
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

			// src/edu/kit/iti/algover/parser/Dafny.g:139:3: ( ensures )*
			loop7:
			while (true) {
				int alt7=2;
				int LA7_0 = input.LA(1);
				if ( (LA7_0==ENSURES) ) {
					alt7=1;
				}

				switch (alt7) {
				case 1 :
					// src/edu/kit/iti/algover/parser/Dafny.g:139:5: ensures
					{
					pushFollow(FOLLOW_ensures_in_method723);
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

			// src/edu/kit/iti/algover/parser/Dafny.g:140:3: ( decreases )?
			int alt8=2;
			int LA8_0 = input.LA(1);
			if ( (LA8_0==DECREASES) ) {
				alt8=1;
			}
			switch (alt8) {
				case 1 :
					// src/edu/kit/iti/algover/parser/Dafny.g:140:5: decreases
					{
					pushFollow(FOLLOW_decreases_in_method732);
					decreases21=decreases();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_decreases.add(decreases21.getTree());
					}
					break;

			}

			char_literal22=(Token)match(input,BLOCK_BEGIN,FOLLOW_BLOCK_BEGIN_in_method739); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_BLOCK_BEGIN.add(char_literal22);

			// src/edu/kit/iti/algover/parser/Dafny.g:141:7: ( statements )?
			int alt9=2;
			int LA9_0 = input.LA(1);
			if ( (LA9_0==ASSERT||LA9_0==ASSUME||(LA9_0 >= ID && LA9_0 <= IF)||LA9_0==LABEL||(LA9_0 >= VAR && LA9_0 <= WHILE)) ) {
				alt9=1;
			}
			switch (alt9) {
				case 1 :
					// src/edu/kit/iti/algover/parser/Dafny.g:141:7: statements
					{
					pushFollow(FOLLOW_statements_in_method741);
					statements23=statements();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_statements.add(statements23.getTree());
					}
					break;

			}

			char_literal24=(Token)match(input,BLOCK_END,FOLLOW_BLOCK_END_in_method744); if (state.failed) return retval; 
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
			// 142:3: -> ^( METHOD[tok] ID ^( ARGS ( vars )? ) ( returns_ )? ( requires )* ( ensures )* ( decreases )? ^( BLOCK ( statements )? ) )
			{
				// src/edu/kit/iti/algover/parser/Dafny.g:143:5: ^( METHOD[tok] ID ^( ARGS ( vars )? ) ( returns_ )? ( requires )* ( ensures )* ( decreases )? ^( BLOCK ( statements )? ) )
				{
				DafnyTree root_1 = (DafnyTree)adaptor.nil();
				root_1 = (DafnyTree)adaptor.becomeRoot((DafnyTree)adaptor.create(METHOD, tok), root_1);
				adaptor.addChild(root_1, stream_ID.nextNode());
				// src/edu/kit/iti/algover/parser/Dafny.g:143:22: ^( ARGS ( vars )? )
				{
				DafnyTree root_2 = (DafnyTree)adaptor.nil();
				root_2 = (DafnyTree)adaptor.becomeRoot((DafnyTree)adaptor.create(ARGS, "ARGS"), root_2);
				// src/edu/kit/iti/algover/parser/Dafny.g:143:29: ( vars )?
				if ( stream_vars.hasNext() ) {
					adaptor.addChild(root_2, stream_vars.nextTree());
				}
				stream_vars.reset();

				adaptor.addChild(root_1, root_2);
				}

				// src/edu/kit/iti/algover/parser/Dafny.g:143:36: ( returns_ )?
				if ( stream_returns_.hasNext() ) {
					adaptor.addChild(root_1, stream_returns_.nextTree());
				}
				stream_returns_.reset();

				// src/edu/kit/iti/algover/parser/Dafny.g:143:46: ( requires )*
				while ( stream_requires.hasNext() ) {
					adaptor.addChild(root_1, stream_requires.nextTree());
				}
				stream_requires.reset();

				// src/edu/kit/iti/algover/parser/Dafny.g:143:56: ( ensures )*
				while ( stream_ensures.hasNext() ) {
					adaptor.addChild(root_1, stream_ensures.nextTree());
				}
				stream_ensures.reset();

				// src/edu/kit/iti/algover/parser/Dafny.g:144:9: ( decreases )?
				if ( stream_decreases.hasNext() ) {
					adaptor.addChild(root_1, stream_decreases.nextTree());
				}
				stream_decreases.reset();

				// src/edu/kit/iti/algover/parser/Dafny.g:144:20: ^( BLOCK ( statements )? )
				{
				DafnyTree root_2 = (DafnyTree)adaptor.nil();
				root_2 = (DafnyTree)adaptor.becomeRoot((DafnyTree)adaptor.create(BLOCK, "BLOCK"), root_2);
				// src/edu/kit/iti/algover/parser/Dafny.g:144:28: ( statements )?
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
	// src/edu/kit/iti/algover/parser/Dafny.g:147:1: function : 'function' ^ ID '(' ! ( vars )? ')' ! ':' ! type '{' ! expression '}' !;
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
			// src/edu/kit/iti/algover/parser/Dafny.g:147:9: ( 'function' ^ ID '(' ! ( vars )? ')' ! ':' ! type '{' ! expression '}' !)
			// src/edu/kit/iti/algover/parser/Dafny.g:148:3: 'function' ^ ID '(' ! ( vars )? ')' ! ':' ! type '{' ! expression '}' !
			{
			root_0 = (DafnyTree)adaptor.nil();


			string_literal25=(Token)match(input,FUNCTION,FOLLOW_FUNCTION_in_function806); if (state.failed) return retval;
			if ( state.backtracking==0 ) {
			string_literal25_tree = (DafnyTree)adaptor.create(string_literal25);
			root_0 = (DafnyTree)adaptor.becomeRoot(string_literal25_tree, root_0);
			}

			ID26=(Token)match(input,ID,FOLLOW_ID_in_function811); if (state.failed) return retval;
			if ( state.backtracking==0 ) {
			ID26_tree = (DafnyTree)adaptor.create(ID26);
			adaptor.addChild(root_0, ID26_tree);
			}

			char_literal27=(Token)match(input,68,FOLLOW_68_in_function813); if (state.failed) return retval;
			// src/edu/kit/iti/algover/parser/Dafny.g:149:11: ( vars )?
			int alt10=2;
			int LA10_0 = input.LA(1);
			if ( (LA10_0==ID) ) {
				alt10=1;
			}
			switch (alt10) {
				case 1 :
					// src/edu/kit/iti/algover/parser/Dafny.g:149:11: vars
					{
					pushFollow(FOLLOW_vars_in_function816);
					vars28=vars();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, vars28.getTree());

					}
					break;

			}

			char_literal29=(Token)match(input,69,FOLLOW_69_in_function819); if (state.failed) return retval;
			char_literal30=(Token)match(input,71,FOLLOW_71_in_function822); if (state.failed) return retval;
			pushFollow(FOLLOW_type_in_function825);
			type31=type();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, type31.getTree());

			char_literal32=(Token)match(input,BLOCK_BEGIN,FOLLOW_BLOCK_BEGIN_in_function829); if (state.failed) return retval;
			pushFollow(FOLLOW_expression_in_function832);
			expression33=expression();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, expression33.getTree());

			char_literal34=(Token)match(input,BLOCK_END,FOLLOW_BLOCK_END_in_function834); if (state.failed) return retval;
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
	// src/edu/kit/iti/algover/parser/Dafny.g:153:1: field : 'var' ID ':' type ';' ;
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
			// src/edu/kit/iti/algover/parser/Dafny.g:153:6: ( 'var' ID ':' type ';' )
			// src/edu/kit/iti/algover/parser/Dafny.g:154:3: 'var' ID ':' type ';'
			{
			root_0 = (DafnyTree)adaptor.nil();


			string_literal35=(Token)match(input,VAR,FOLLOW_VAR_in_field847); if (state.failed) return retval;
			if ( state.backtracking==0 ) {
			string_literal35_tree = (DafnyTree)adaptor.create(string_literal35);
			adaptor.addChild(root_0, string_literal35_tree);
			}

			ID36=(Token)match(input,ID,FOLLOW_ID_in_field849); if (state.failed) return retval;
			if ( state.backtracking==0 ) {
			ID36_tree = (DafnyTree)adaptor.create(ID36);
			adaptor.addChild(root_0, ID36_tree);
			}

			char_literal37=(Token)match(input,71,FOLLOW_71_in_field851); if (state.failed) return retval;
			if ( state.backtracking==0 ) {
			char_literal37_tree = (DafnyTree)adaptor.create(char_literal37);
			adaptor.addChild(root_0, char_literal37_tree);
			}

			pushFollow(FOLLOW_type_in_field853);
			type38=type();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, type38.getTree());

			char_literal39=(Token)match(input,72,FOLLOW_72_in_field855); if (state.failed) return retval;
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
	// src/edu/kit/iti/algover/parser/Dafny.g:157:1: vars : var ( ',' ! var )* ;
	public final DafnyParser.vars_return vars() throws RecognitionException {
		DafnyParser.vars_return retval = new DafnyParser.vars_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		Token char_literal41=null;
		ParserRuleReturnScope var40 =null;
		ParserRuleReturnScope var42 =null;

		DafnyTree char_literal41_tree=null;

		try {
			// src/edu/kit/iti/algover/parser/Dafny.g:157:5: ( var ( ',' ! var )* )
			// src/edu/kit/iti/algover/parser/Dafny.g:158:3: var ( ',' ! var )*
			{
			root_0 = (DafnyTree)adaptor.nil();


			pushFollow(FOLLOW_var_in_vars867);
			var40=var();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, var40.getTree());

			// src/edu/kit/iti/algover/parser/Dafny.g:159:3: ( ',' ! var )*
			loop11:
			while (true) {
				int alt11=2;
				int LA11_0 = input.LA(1);
				if ( (LA11_0==70) ) {
					alt11=1;
				}

				switch (alt11) {
				case 1 :
					// src/edu/kit/iti/algover/parser/Dafny.g:159:5: ',' ! var
					{
					char_literal41=(Token)match(input,70,FOLLOW_70_in_vars873); if (state.failed) return retval;
					pushFollow(FOLLOW_var_in_vars876);
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
	// src/edu/kit/iti/algover/parser/Dafny.g:162:1: var : ID ':' type -> ^( VAR ID type ) ;
	public final DafnyParser.var_return var() throws RecognitionException {
		DafnyParser.var_return retval = new DafnyParser.var_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		Token ID43=null;
		Token char_literal44=null;
		ParserRuleReturnScope type45 =null;

		DafnyTree ID43_tree=null;
		DafnyTree char_literal44_tree=null;
		RewriteRuleTokenStream stream_71=new RewriteRuleTokenStream(adaptor,"token 71");
		RewriteRuleTokenStream stream_ID=new RewriteRuleTokenStream(adaptor,"token ID");
		RewriteRuleSubtreeStream stream_type=new RewriteRuleSubtreeStream(adaptor,"rule type");

		try {
			// src/edu/kit/iti/algover/parser/Dafny.g:162:4: ( ID ':' type -> ^( VAR ID type ) )
			// src/edu/kit/iti/algover/parser/Dafny.g:163:3: ID ':' type
			{
			ID43=(Token)match(input,ID,FOLLOW_ID_in_var891); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_ID.add(ID43);

			char_literal44=(Token)match(input,71,FOLLOW_71_in_var893); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_71.add(char_literal44);

			pushFollow(FOLLOW_type_in_var895);
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
			// 163:15: -> ^( VAR ID type )
			{
				// src/edu/kit/iti/algover/parser/Dafny.g:163:18: ^( VAR ID type )
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
	// src/edu/kit/iti/algover/parser/Dafny.g:166:1: type : ( INT | BOOL | SET ^ '<' ! INT '>' !| ARRAY ^ '<' ! INT '>' !);
	public final DafnyParser.type_return type() throws RecognitionException {
		DafnyParser.type_return retval = new DafnyParser.type_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		Token INT46=null;
		Token BOOL47=null;
		Token SET48=null;
		Token char_literal49=null;
		Token INT50=null;
		Token char_literal51=null;
		Token ARRAY52=null;
		Token char_literal53=null;
		Token INT54=null;
		Token char_literal55=null;

		DafnyTree INT46_tree=null;
		DafnyTree BOOL47_tree=null;
		DafnyTree SET48_tree=null;
		DafnyTree char_literal49_tree=null;
		DafnyTree INT50_tree=null;
		DafnyTree char_literal51_tree=null;
		DafnyTree ARRAY52_tree=null;
		DafnyTree char_literal53_tree=null;
		DafnyTree INT54_tree=null;
		DafnyTree char_literal55_tree=null;

		try {
			// src/edu/kit/iti/algover/parser/Dafny.g:166:5: ( INT | BOOL | SET ^ '<' ! INT '>' !| ARRAY ^ '<' ! INT '>' !)
			int alt12=4;
			switch ( input.LA(1) ) {
			case INT:
				{
				alt12=1;
				}
				break;
			case BOOL:
				{
				alt12=2;
				}
				break;
			case SET:
				{
				alt12=3;
				}
				break;
			case ARRAY:
				{
				alt12=4;
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
					// src/edu/kit/iti/algover/parser/Dafny.g:167:5: INT
					{
					root_0 = (DafnyTree)adaptor.nil();


					INT46=(Token)match(input,INT,FOLLOW_INT_in_type919); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					INT46_tree = (DafnyTree)adaptor.create(INT46);
					adaptor.addChild(root_0, INT46_tree);
					}

					}
					break;
				case 2 :
					// src/edu/kit/iti/algover/parser/Dafny.g:167:11: BOOL
					{
					root_0 = (DafnyTree)adaptor.nil();


					BOOL47=(Token)match(input,BOOL,FOLLOW_BOOL_in_type923); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					BOOL47_tree = (DafnyTree)adaptor.create(BOOL47);
					adaptor.addChild(root_0, BOOL47_tree);
					}

					}
					break;
				case 3 :
					// src/edu/kit/iti/algover/parser/Dafny.g:167:18: SET ^ '<' ! INT '>' !
					{
					root_0 = (DafnyTree)adaptor.nil();


					SET48=(Token)match(input,SET,FOLLOW_SET_in_type927); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					SET48_tree = (DafnyTree)adaptor.create(SET48);
					root_0 = (DafnyTree)adaptor.becomeRoot(SET48_tree, root_0);
					}

					char_literal49=(Token)match(input,LT,FOLLOW_LT_in_type930); if (state.failed) return retval;
					INT50=(Token)match(input,INT,FOLLOW_INT_in_type933); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					INT50_tree = (DafnyTree)adaptor.create(INT50);
					adaptor.addChild(root_0, INT50_tree);
					}

					char_literal51=(Token)match(input,GT,FOLLOW_GT_in_type935); if (state.failed) return retval;
					}
					break;
				case 4 :
					// src/edu/kit/iti/algover/parser/Dafny.g:168:5: ARRAY ^ '<' ! INT '>' !
					{
					root_0 = (DafnyTree)adaptor.nil();


					ARRAY52=(Token)match(input,ARRAY,FOLLOW_ARRAY_in_type942); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					ARRAY52_tree = (DafnyTree)adaptor.create(ARRAY52);
					root_0 = (DafnyTree)adaptor.becomeRoot(ARRAY52_tree, root_0);
					}

					char_literal53=(Token)match(input,LT,FOLLOW_LT_in_type945); if (state.failed) return retval;
					INT54=(Token)match(input,INT,FOLLOW_INT_in_type948); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					INT54_tree = (DafnyTree)adaptor.create(INT54);
					adaptor.addChild(root_0, INT54_tree);
					}

					char_literal55=(Token)match(input,GT,FOLLOW_GT_in_type950); if (state.failed) return retval;
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
	// src/edu/kit/iti/algover/parser/Dafny.g:171:1: returns_ : RETURNS ^ '(' ! vars ')' !;
	public final DafnyParser.returns__return returns_() throws RecognitionException {
		DafnyParser.returns__return retval = new DafnyParser.returns__return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		Token RETURNS56=null;
		Token char_literal57=null;
		Token char_literal59=null;
		ParserRuleReturnScope vars58 =null;

		DafnyTree RETURNS56_tree=null;
		DafnyTree char_literal57_tree=null;
		DafnyTree char_literal59_tree=null;

		try {
			// src/edu/kit/iti/algover/parser/Dafny.g:171:9: ( RETURNS ^ '(' ! vars ')' !)
			// src/edu/kit/iti/algover/parser/Dafny.g:172:3: RETURNS ^ '(' ! vars ')' !
			{
			root_0 = (DafnyTree)adaptor.nil();


			RETURNS56=(Token)match(input,RETURNS,FOLLOW_RETURNS_in_returns_963); if (state.failed) return retval;
			if ( state.backtracking==0 ) {
			RETURNS56_tree = (DafnyTree)adaptor.create(RETURNS56);
			root_0 = (DafnyTree)adaptor.becomeRoot(RETURNS56_tree, root_0);
			}

			char_literal57=(Token)match(input,68,FOLLOW_68_in_returns_966); if (state.failed) return retval;
			pushFollow(FOLLOW_vars_in_returns_969);
			vars58=vars();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, vars58.getTree());

			char_literal59=(Token)match(input,69,FOLLOW_69_in_returns_971); if (state.failed) return retval;
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
	// src/edu/kit/iti/algover/parser/Dafny.g:175:1: requires : REQUIRES ^ ( label )? expression ;
	public final DafnyParser.requires_return requires() throws RecognitionException {
		DafnyParser.requires_return retval = new DafnyParser.requires_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		Token REQUIRES60=null;
		ParserRuleReturnScope label61 =null;
		ParserRuleReturnScope expression62 =null;

		DafnyTree REQUIRES60_tree=null;

		try {
			// src/edu/kit/iti/algover/parser/Dafny.g:175:9: ( REQUIRES ^ ( label )? expression )
			// src/edu/kit/iti/algover/parser/Dafny.g:176:3: REQUIRES ^ ( label )? expression
			{
			root_0 = (DafnyTree)adaptor.nil();


			REQUIRES60=(Token)match(input,REQUIRES,FOLLOW_REQUIRES_in_requires984); if (state.failed) return retval;
			if ( state.backtracking==0 ) {
			REQUIRES60_tree = (DafnyTree)adaptor.create(REQUIRES60);
			root_0 = (DafnyTree)adaptor.becomeRoot(REQUIRES60_tree, root_0);
			}

			// src/edu/kit/iti/algover/parser/Dafny.g:176:13: ( label )?
			int alt13=2;
			int LA13_0 = input.LA(1);
			if ( (LA13_0==LABEL) ) {
				alt13=1;
			}
			switch (alt13) {
				case 1 :
					// src/edu/kit/iti/algover/parser/Dafny.g:176:13: label
					{
					pushFollow(FOLLOW_label_in_requires987);
					label61=label();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, label61.getTree());

					}
					break;

			}

			pushFollow(FOLLOW_expression_in_requires990);
			expression62=expression();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, expression62.getTree());

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
	// src/edu/kit/iti/algover/parser/Dafny.g:179:1: ensures : ENSURES ^ ( label )? expression ;
	public final DafnyParser.ensures_return ensures() throws RecognitionException {
		DafnyParser.ensures_return retval = new DafnyParser.ensures_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		Token ENSURES63=null;
		ParserRuleReturnScope label64 =null;
		ParserRuleReturnScope expression65 =null;

		DafnyTree ENSURES63_tree=null;

		try {
			// src/edu/kit/iti/algover/parser/Dafny.g:179:8: ( ENSURES ^ ( label )? expression )
			// src/edu/kit/iti/algover/parser/Dafny.g:180:3: ENSURES ^ ( label )? expression
			{
			root_0 = (DafnyTree)adaptor.nil();


			ENSURES63=(Token)match(input,ENSURES,FOLLOW_ENSURES_in_ensures1002); if (state.failed) return retval;
			if ( state.backtracking==0 ) {
			ENSURES63_tree = (DafnyTree)adaptor.create(ENSURES63);
			root_0 = (DafnyTree)adaptor.becomeRoot(ENSURES63_tree, root_0);
			}

			// src/edu/kit/iti/algover/parser/Dafny.g:180:12: ( label )?
			int alt14=2;
			int LA14_0 = input.LA(1);
			if ( (LA14_0==LABEL) ) {
				alt14=1;
			}
			switch (alt14) {
				case 1 :
					// src/edu/kit/iti/algover/parser/Dafny.g:180:12: label
					{
					pushFollow(FOLLOW_label_in_ensures1005);
					label64=label();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, label64.getTree());

					}
					break;

			}

			pushFollow(FOLLOW_expression_in_ensures1008);
			expression65=expression();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, expression65.getTree());

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
	// src/edu/kit/iti/algover/parser/Dafny.g:183:1: decreases : DECREASES ^ expression ;
	public final DafnyParser.decreases_return decreases() throws RecognitionException {
		DafnyParser.decreases_return retval = new DafnyParser.decreases_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		Token DECREASES66=null;
		ParserRuleReturnScope expression67 =null;

		DafnyTree DECREASES66_tree=null;

		try {
			// src/edu/kit/iti/algover/parser/Dafny.g:183:10: ( DECREASES ^ expression )
			// src/edu/kit/iti/algover/parser/Dafny.g:184:3: DECREASES ^ expression
			{
			root_0 = (DafnyTree)adaptor.nil();


			DECREASES66=(Token)match(input,DECREASES,FOLLOW_DECREASES_in_decreases1020); if (state.failed) return retval;
			if ( state.backtracking==0 ) {
			DECREASES66_tree = (DafnyTree)adaptor.create(DECREASES66);
			root_0 = (DafnyTree)adaptor.becomeRoot(DECREASES66_tree, root_0);
			}

			pushFollow(FOLLOW_expression_in_decreases1023);
			expression67=expression();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, expression67.getTree());

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
	// src/edu/kit/iti/algover/parser/Dafny.g:187:1: invariant : INVARIANT ^ ( label )? expression ;
	public final DafnyParser.invariant_return invariant() throws RecognitionException {
		DafnyParser.invariant_return retval = new DafnyParser.invariant_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		Token INVARIANT68=null;
		ParserRuleReturnScope label69 =null;
		ParserRuleReturnScope expression70 =null;

		DafnyTree INVARIANT68_tree=null;

		try {
			// src/edu/kit/iti/algover/parser/Dafny.g:187:10: ( INVARIANT ^ ( label )? expression )
			// src/edu/kit/iti/algover/parser/Dafny.g:188:3: INVARIANT ^ ( label )? expression
			{
			root_0 = (DafnyTree)adaptor.nil();


			INVARIANT68=(Token)match(input,INVARIANT,FOLLOW_INVARIANT_in_invariant1035); if (state.failed) return retval;
			if ( state.backtracking==0 ) {
			INVARIANT68_tree = (DafnyTree)adaptor.create(INVARIANT68);
			root_0 = (DafnyTree)adaptor.becomeRoot(INVARIANT68_tree, root_0);
			}

			// src/edu/kit/iti/algover/parser/Dafny.g:188:14: ( label )?
			int alt15=2;
			int LA15_0 = input.LA(1);
			if ( (LA15_0==LABEL) ) {
				alt15=1;
			}
			switch (alt15) {
				case 1 :
					// src/edu/kit/iti/algover/parser/Dafny.g:188:14: label
					{
					pushFollow(FOLLOW_label_in_invariant1038);
					label69=label();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, label69.getTree());

					}
					break;

			}

			pushFollow(FOLLOW_expression_in_invariant1041);
			expression70=expression();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, expression70.getTree());

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
	// src/edu/kit/iti/algover/parser/Dafny.g:191:1: modifies : MODIFIES ^ expressions ;
	public final DafnyParser.modifies_return modifies() throws RecognitionException {
		DafnyParser.modifies_return retval = new DafnyParser.modifies_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		Token MODIFIES71=null;
		ParserRuleReturnScope expressions72 =null;

		DafnyTree MODIFIES71_tree=null;

		try {
			// src/edu/kit/iti/algover/parser/Dafny.g:191:9: ( MODIFIES ^ expressions )
			// src/edu/kit/iti/algover/parser/Dafny.g:192:3: MODIFIES ^ expressions
			{
			root_0 = (DafnyTree)adaptor.nil();


			MODIFIES71=(Token)match(input,MODIFIES,FOLLOW_MODIFIES_in_modifies1053); if (state.failed) return retval;
			if ( state.backtracking==0 ) {
			MODIFIES71_tree = (DafnyTree)adaptor.create(MODIFIES71);
			root_0 = (DafnyTree)adaptor.becomeRoot(MODIFIES71_tree, root_0);
			}

			pushFollow(FOLLOW_expressions_in_modifies1056);
			expressions72=expressions();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, expressions72.getTree());

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
	// src/edu/kit/iti/algover/parser/Dafny.g:195:1: block : '{' ( statements )? '}' -> ^( BLOCK ( statements )? ) ;
	public final DafnyParser.block_return block() throws RecognitionException {
		DafnyParser.block_return retval = new DafnyParser.block_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		Token char_literal73=null;
		Token char_literal75=null;
		ParserRuleReturnScope statements74 =null;

		DafnyTree char_literal73_tree=null;
		DafnyTree char_literal75_tree=null;
		RewriteRuleTokenStream stream_BLOCK_END=new RewriteRuleTokenStream(adaptor,"token BLOCK_END");
		RewriteRuleTokenStream stream_BLOCK_BEGIN=new RewriteRuleTokenStream(adaptor,"token BLOCK_BEGIN");
		RewriteRuleSubtreeStream stream_statements=new RewriteRuleSubtreeStream(adaptor,"rule statements");

		try {
			// src/edu/kit/iti/algover/parser/Dafny.g:195:6: ( '{' ( statements )? '}' -> ^( BLOCK ( statements )? ) )
			// src/edu/kit/iti/algover/parser/Dafny.g:196:3: '{' ( statements )? '}'
			{
			char_literal73=(Token)match(input,BLOCK_BEGIN,FOLLOW_BLOCK_BEGIN_in_block1068); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_BLOCK_BEGIN.add(char_literal73);

			// src/edu/kit/iti/algover/parser/Dafny.g:196:7: ( statements )?
			int alt16=2;
			int LA16_0 = input.LA(1);
			if ( (LA16_0==ASSERT||LA16_0==ASSUME||(LA16_0 >= ID && LA16_0 <= IF)||LA16_0==LABEL||(LA16_0 >= VAR && LA16_0 <= WHILE)) ) {
				alt16=1;
			}
			switch (alt16) {
				case 1 :
					// src/edu/kit/iti/algover/parser/Dafny.g:196:7: statements
					{
					pushFollow(FOLLOW_statements_in_block1070);
					statements74=statements();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_statements.add(statements74.getTree());
					}
					break;

			}

			char_literal75=(Token)match(input,BLOCK_END,FOLLOW_BLOCK_END_in_block1073); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_BLOCK_END.add(char_literal75);

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
			// 196:23: -> ^( BLOCK ( statements )? )
			{
				// src/edu/kit/iti/algover/parser/Dafny.g:196:26: ^( BLOCK ( statements )? )
				{
				DafnyTree root_1 = (DafnyTree)adaptor.nil();
				root_1 = (DafnyTree)adaptor.becomeRoot((DafnyTree)adaptor.create(BLOCK, "BLOCK"), root_1);
				// src/edu/kit/iti/algover/parser/Dafny.g:196:34: ( statements )?
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
	// src/edu/kit/iti/algover/parser/Dafny.g:199:1: relaxedBlock : ( block | statement -> ^( BLOCK statement ) );
	public final DafnyParser.relaxedBlock_return relaxedBlock() throws RecognitionException {
		DafnyParser.relaxedBlock_return retval = new DafnyParser.relaxedBlock_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		ParserRuleReturnScope block76 =null;
		ParserRuleReturnScope statement77 =null;

		RewriteRuleSubtreeStream stream_statement=new RewriteRuleSubtreeStream(adaptor,"rule statement");

		try {
			// src/edu/kit/iti/algover/parser/Dafny.g:199:13: ( block | statement -> ^( BLOCK statement ) )
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
					// src/edu/kit/iti/algover/parser/Dafny.g:200:5: block
					{
					root_0 = (DafnyTree)adaptor.nil();


					pushFollow(FOLLOW_block_in_relaxedBlock1096);
					block76=block();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, block76.getTree());

					}
					break;
				case 2 :
					// src/edu/kit/iti/algover/parser/Dafny.g:201:5: statement
					{
					pushFollow(FOLLOW_statement_in_relaxedBlock1102);
					statement77=statement();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_statement.add(statement77.getTree());
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
					// 201:15: -> ^( BLOCK statement )
					{
						// src/edu/kit/iti/algover/parser/Dafny.g:201:18: ^( BLOCK statement )
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
	// src/edu/kit/iti/algover/parser/Dafny.g:204:1: statements : ( statement )+ ;
	public final DafnyParser.statements_return statements() throws RecognitionException {
		DafnyParser.statements_return retval = new DafnyParser.statements_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		ParserRuleReturnScope statement78 =null;


		try {
			// src/edu/kit/iti/algover/parser/Dafny.g:204:11: ( ( statement )+ )
			// src/edu/kit/iti/algover/parser/Dafny.g:205:3: ( statement )+
			{
			root_0 = (DafnyTree)adaptor.nil();


			// src/edu/kit/iti/algover/parser/Dafny.g:205:3: ( statement )+
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
					// src/edu/kit/iti/algover/parser/Dafny.g:205:5: statement
					{
					pushFollow(FOLLOW_statement_in_statements1124);
					statement78=statement();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, statement78.getTree());

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
	// src/edu/kit/iti/algover/parser/Dafny.g:208:1: statement : ( VAR ^ ID ':' ! type ( ':=' ! expression )? ';' !| ID ass= ':=' '*' ';' -> ^( HAVOC[$ass] ID ) | ID ':=' ^ expression ';' !| ID '[' i= expression ']' ass= ':=' v= expression ';' -> ^( ARRAY_UPDATE[$ass] ID $i $v) | ( ID ':=' 'call' )=>r= ID ':=' 'call' f= ID '(' ( expressions )? ')' ';' -> ^( 'call' $f ^( RESULTS $r) ^( ARGS ( expressions )? ) ) | ids ':=' 'call' ID '(' ( expressions )? ')' ';' -> ^( 'call' ID ^( RESULTS ids ) ^( ARGS ( expressions )? ) ) | ( label )? 'while' expression ( invariant )+ ( modifies )? decreases relaxedBlock -> ^( 'while' ( label )? expression ( invariant )+ ( modifies )? decreases relaxedBlock ) | ( label )? 'if' ^ expression relaxedBlock ( options {greedy=true; } : 'else' ! relaxedBlock )? | 'assert' ^ ( 'label' ! ID ':' !)? expression ';' !| 'assume' ^ ( 'label' ! ID ':' !)? expression ';' !);
	public final DafnyParser.statement_return statement() throws RecognitionException {
		DafnyParser.statement_return retval = new DafnyParser.statement_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		Token ass=null;
		Token r=null;
		Token f=null;
		Token VAR79=null;
		Token ID80=null;
		Token char_literal81=null;
		Token string_literal83=null;
		Token char_literal85=null;
		Token ID86=null;
		Token char_literal87=null;
		Token char_literal88=null;
		Token ID89=null;
		Token string_literal90=null;
		Token char_literal92=null;
		Token ID93=null;
		Token char_literal94=null;
		Token char_literal95=null;
		Token char_literal96=null;
		Token string_literal97=null;
		Token string_literal98=null;
		Token char_literal99=null;
		Token char_literal101=null;
		Token char_literal102=null;
		Token string_literal104=null;
		Token string_literal105=null;
		Token ID106=null;
		Token char_literal107=null;
		Token char_literal109=null;
		Token char_literal110=null;
		Token string_literal112=null;
		Token string_literal119=null;
		Token string_literal122=null;
		Token string_literal124=null;
		Token string_literal125=null;
		Token ID126=null;
		Token char_literal127=null;
		Token char_literal129=null;
		Token string_literal130=null;
		Token string_literal131=null;
		Token ID132=null;
		Token char_literal133=null;
		Token char_literal135=null;
		ParserRuleReturnScope i =null;
		ParserRuleReturnScope v =null;
		ParserRuleReturnScope type82 =null;
		ParserRuleReturnScope expression84 =null;
		ParserRuleReturnScope expression91 =null;
		ParserRuleReturnScope expressions100 =null;
		ParserRuleReturnScope ids103 =null;
		ParserRuleReturnScope expressions108 =null;
		ParserRuleReturnScope label111 =null;
		ParserRuleReturnScope expression113 =null;
		ParserRuleReturnScope invariant114 =null;
		ParserRuleReturnScope modifies115 =null;
		ParserRuleReturnScope decreases116 =null;
		ParserRuleReturnScope relaxedBlock117 =null;
		ParserRuleReturnScope label118 =null;
		ParserRuleReturnScope expression120 =null;
		ParserRuleReturnScope relaxedBlock121 =null;
		ParserRuleReturnScope relaxedBlock123 =null;
		ParserRuleReturnScope expression128 =null;
		ParserRuleReturnScope expression134 =null;

		DafnyTree ass_tree=null;
		DafnyTree r_tree=null;
		DafnyTree f_tree=null;
		DafnyTree VAR79_tree=null;
		DafnyTree ID80_tree=null;
		DafnyTree char_literal81_tree=null;
		DafnyTree string_literal83_tree=null;
		DafnyTree char_literal85_tree=null;
		DafnyTree ID86_tree=null;
		DafnyTree char_literal87_tree=null;
		DafnyTree char_literal88_tree=null;
		DafnyTree ID89_tree=null;
		DafnyTree string_literal90_tree=null;
		DafnyTree char_literal92_tree=null;
		DafnyTree ID93_tree=null;
		DafnyTree char_literal94_tree=null;
		DafnyTree char_literal95_tree=null;
		DafnyTree char_literal96_tree=null;
		DafnyTree string_literal97_tree=null;
		DafnyTree string_literal98_tree=null;
		DafnyTree char_literal99_tree=null;
		DafnyTree char_literal101_tree=null;
		DafnyTree char_literal102_tree=null;
		DafnyTree string_literal104_tree=null;
		DafnyTree string_literal105_tree=null;
		DafnyTree ID106_tree=null;
		DafnyTree char_literal107_tree=null;
		DafnyTree char_literal109_tree=null;
		DafnyTree char_literal110_tree=null;
		DafnyTree string_literal112_tree=null;
		DafnyTree string_literal119_tree=null;
		DafnyTree string_literal122_tree=null;
		DafnyTree string_literal124_tree=null;
		DafnyTree string_literal125_tree=null;
		DafnyTree ID126_tree=null;
		DafnyTree char_literal127_tree=null;
		DafnyTree char_literal129_tree=null;
		DafnyTree string_literal130_tree=null;
		DafnyTree string_literal131_tree=null;
		DafnyTree ID132_tree=null;
		DafnyTree char_literal133_tree=null;
		DafnyTree char_literal135_tree=null;
		RewriteRuleTokenStream stream_CALL=new RewriteRuleTokenStream(adaptor,"token CALL");
		RewriteRuleTokenStream stream_68=new RewriteRuleTokenStream(adaptor,"token 68");
		RewriteRuleTokenStream stream_69=new RewriteRuleTokenStream(adaptor,"token 69");
		RewriteRuleTokenStream stream_TIMES=new RewriteRuleTokenStream(adaptor,"token TIMES");
		RewriteRuleTokenStream stream_WHILE=new RewriteRuleTokenStream(adaptor,"token WHILE");
		RewriteRuleTokenStream stream_72=new RewriteRuleTokenStream(adaptor,"token 72");
		RewriteRuleTokenStream stream_ID=new RewriteRuleTokenStream(adaptor,"token ID");
		RewriteRuleTokenStream stream_ASSIGN=new RewriteRuleTokenStream(adaptor,"token ASSIGN");
		RewriteRuleTokenStream stream_73=new RewriteRuleTokenStream(adaptor,"token 73");
		RewriteRuleTokenStream stream_74=new RewriteRuleTokenStream(adaptor,"token 74");
		RewriteRuleSubtreeStream stream_expression=new RewriteRuleSubtreeStream(adaptor,"rule expression");
		RewriteRuleSubtreeStream stream_decreases=new RewriteRuleSubtreeStream(adaptor,"rule decreases");
		RewriteRuleSubtreeStream stream_relaxedBlock=new RewriteRuleSubtreeStream(adaptor,"rule relaxedBlock");
		RewriteRuleSubtreeStream stream_modifies=new RewriteRuleSubtreeStream(adaptor,"rule modifies");
		RewriteRuleSubtreeStream stream_ids=new RewriteRuleSubtreeStream(adaptor,"rule ids");
		RewriteRuleSubtreeStream stream_label=new RewriteRuleSubtreeStream(adaptor,"rule label");
		RewriteRuleSubtreeStream stream_expressions=new RewriteRuleSubtreeStream(adaptor,"rule expressions");
		RewriteRuleSubtreeStream stream_invariant=new RewriteRuleSubtreeStream(adaptor,"rule invariant");

		try {
			// src/edu/kit/iti/algover/parser/Dafny.g:208:10: ( VAR ^ ID ':' ! type ( ':=' ! expression )? ';' !| ID ass= ':=' '*' ';' -> ^( HAVOC[$ass] ID ) | ID ':=' ^ expression ';' !| ID '[' i= expression ']' ass= ':=' v= expression ';' -> ^( ARRAY_UPDATE[$ass] ID $i $v) | ( ID ':=' 'call' )=>r= ID ':=' 'call' f= ID '(' ( expressions )? ')' ';' -> ^( 'call' $f ^( RESULTS $r) ^( ARGS ( expressions )? ) ) | ids ':=' 'call' ID '(' ( expressions )? ')' ';' -> ^( 'call' ID ^( RESULTS ids ) ^( ARGS ( expressions )? ) ) | ( label )? 'while' expression ( invariant )+ ( modifies )? decreases relaxedBlock -> ^( 'while' ( label )? expression ( invariant )+ ( modifies )? decreases relaxedBlock ) | ( label )? 'if' ^ expression relaxedBlock ( options {greedy=true; } : 'else' ! relaxedBlock )? | 'assert' ^ ( 'label' ! ID ':' !)? expression ';' !| 'assume' ^ ( 'label' ! ID ':' !)? expression ';' !)
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
					else if ( (LA29_8==BLOCK_BEGIN||LA29_8==ID||LA29_8==LIT||LA29_8==MINUS||(LA29_8 >= NOT && LA29_8 <= NULL)||LA29_8==THIS||LA29_8==68||LA29_8==73) ) {
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
				case 73:
					{
					alt29=4;
					}
					break;
				case 70:
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
					if ( (LA29_11==71) ) {
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
					// src/edu/kit/iti/algover/parser/Dafny.g:209:5: VAR ^ ID ':' ! type ( ':=' ! expression )? ';' !
					{
					root_0 = (DafnyTree)adaptor.nil();


					VAR79=(Token)match(input,VAR,FOLLOW_VAR_in_statement1141); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					VAR79_tree = (DafnyTree)adaptor.create(VAR79);
					root_0 = (DafnyTree)adaptor.becomeRoot(VAR79_tree, root_0);
					}

					ID80=(Token)match(input,ID,FOLLOW_ID_in_statement1144); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					ID80_tree = (DafnyTree)adaptor.create(ID80);
					adaptor.addChild(root_0, ID80_tree);
					}

					char_literal81=(Token)match(input,71,FOLLOW_71_in_statement1146); if (state.failed) return retval;
					pushFollow(FOLLOW_type_in_statement1149);
					type82=type();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, type82.getTree());

					// src/edu/kit/iti/algover/parser/Dafny.g:209:23: ( ':=' ! expression )?
					int alt19=2;
					int LA19_0 = input.LA(1);
					if ( (LA19_0==ASSIGN) ) {
						alt19=1;
					}
					switch (alt19) {
						case 1 :
							// src/edu/kit/iti/algover/parser/Dafny.g:209:24: ':=' ! expression
							{
							string_literal83=(Token)match(input,ASSIGN,FOLLOW_ASSIGN_in_statement1152); if (state.failed) return retval;
							pushFollow(FOLLOW_expression_in_statement1155);
							expression84=expression();
							state._fsp--;
							if (state.failed) return retval;
							if ( state.backtracking==0 ) adaptor.addChild(root_0, expression84.getTree());

							}
							break;

					}

					char_literal85=(Token)match(input,72,FOLLOW_72_in_statement1159); if (state.failed) return retval;
					}
					break;
				case 2 :
					// src/edu/kit/iti/algover/parser/Dafny.g:210:5: ID ass= ':=' '*' ';'
					{
					ID86=(Token)match(input,ID,FOLLOW_ID_in_statement1166); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_ID.add(ID86);

					ass=(Token)match(input,ASSIGN,FOLLOW_ASSIGN_in_statement1170); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_ASSIGN.add(ass);

					char_literal87=(Token)match(input,TIMES,FOLLOW_TIMES_in_statement1172); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_TIMES.add(char_literal87);

					char_literal88=(Token)match(input,72,FOLLOW_72_in_statement1174); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_72.add(char_literal88);

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
					// 210:25: -> ^( HAVOC[$ass] ID )
					{
						// src/edu/kit/iti/algover/parser/Dafny.g:210:28: ^( HAVOC[$ass] ID )
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
					// src/edu/kit/iti/algover/parser/Dafny.g:211:5: ID ':=' ^ expression ';' !
					{
					root_0 = (DafnyTree)adaptor.nil();


					ID89=(Token)match(input,ID,FOLLOW_ID_in_statement1189); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					ID89_tree = (DafnyTree)adaptor.create(ID89);
					adaptor.addChild(root_0, ID89_tree);
					}

					string_literal90=(Token)match(input,ASSIGN,FOLLOW_ASSIGN_in_statement1191); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					string_literal90_tree = (DafnyTree)adaptor.create(string_literal90);
					root_0 = (DafnyTree)adaptor.becomeRoot(string_literal90_tree, root_0);
					}

					pushFollow(FOLLOW_expression_in_statement1194);
					expression91=expression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, expression91.getTree());

					char_literal92=(Token)match(input,72,FOLLOW_72_in_statement1196); if (state.failed) return retval;
					}
					break;
				case 4 :
					// src/edu/kit/iti/algover/parser/Dafny.g:212:5: ID '[' i= expression ']' ass= ':=' v= expression ';'
					{
					ID93=(Token)match(input,ID,FOLLOW_ID_in_statement1203); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_ID.add(ID93);

					char_literal94=(Token)match(input,73,FOLLOW_73_in_statement1205); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_73.add(char_literal94);

					pushFollow(FOLLOW_expression_in_statement1209);
					i=expression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_expression.add(i.getTree());
					char_literal95=(Token)match(input,74,FOLLOW_74_in_statement1211); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_74.add(char_literal95);

					ass=(Token)match(input,ASSIGN,FOLLOW_ASSIGN_in_statement1215); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_ASSIGN.add(ass);

					pushFollow(FOLLOW_expression_in_statement1219);
					v=expression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_expression.add(v.getTree());
					char_literal96=(Token)match(input,72,FOLLOW_72_in_statement1221); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_72.add(char_literal96);

					// AST REWRITE
					// elements: v, i, ID
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
					// 213:9: -> ^( ARRAY_UPDATE[$ass] ID $i $v)
					{
						// src/edu/kit/iti/algover/parser/Dafny.g:213:12: ^( ARRAY_UPDATE[$ass] ID $i $v)
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
					// src/edu/kit/iti/algover/parser/Dafny.g:214:5: ( ID ':=' 'call' )=>r= ID ':=' 'call' f= ID '(' ( expressions )? ')' ';'
					{
					r=(Token)match(input,ID,FOLLOW_ID_in_statement1262); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_ID.add(r);

					string_literal97=(Token)match(input,ASSIGN,FOLLOW_ASSIGN_in_statement1264); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_ASSIGN.add(string_literal97);

					string_literal98=(Token)match(input,CALL,FOLLOW_CALL_in_statement1266); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_CALL.add(string_literal98);

					f=(Token)match(input,ID,FOLLOW_ID_in_statement1270); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_ID.add(f);

					char_literal99=(Token)match(input,68,FOLLOW_68_in_statement1272); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_68.add(char_literal99);

					// src/edu/kit/iti/algover/parser/Dafny.g:214:51: ( expressions )?
					int alt20=2;
					int LA20_0 = input.LA(1);
					if ( (LA20_0==BLOCK_BEGIN||LA20_0==ID||LA20_0==LIT||LA20_0==MINUS||(LA20_0 >= NOT && LA20_0 <= NULL)||LA20_0==THIS||LA20_0==68||LA20_0==73) ) {
						alt20=1;
					}
					switch (alt20) {
						case 1 :
							// src/edu/kit/iti/algover/parser/Dafny.g:214:51: expressions
							{
							pushFollow(FOLLOW_expressions_in_statement1274);
							expressions100=expressions();
							state._fsp--;
							if (state.failed) return retval;
							if ( state.backtracking==0 ) stream_expressions.add(expressions100.getTree());
							}
							break;

					}

					char_literal101=(Token)match(input,69,FOLLOW_69_in_statement1277); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_69.add(char_literal101);

					char_literal102=(Token)match(input,72,FOLLOW_72_in_statement1279); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_72.add(char_literal102);

					// AST REWRITE
					// elements: r, CALL, f, expressions
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
					// 215:9: -> ^( 'call' $f ^( RESULTS $r) ^( ARGS ( expressions )? ) )
					{
						// src/edu/kit/iti/algover/parser/Dafny.g:215:12: ^( 'call' $f ^( RESULTS $r) ^( ARGS ( expressions )? ) )
						{
						DafnyTree root_1 = (DafnyTree)adaptor.nil();
						root_1 = (DafnyTree)adaptor.becomeRoot(stream_CALL.nextNode(), root_1);
						adaptor.addChild(root_1, stream_f.nextNode());
						// src/edu/kit/iti/algover/parser/Dafny.g:215:24: ^( RESULTS $r)
						{
						DafnyTree root_2 = (DafnyTree)adaptor.nil();
						root_2 = (DafnyTree)adaptor.becomeRoot((DafnyTree)adaptor.create(RESULTS, "RESULTS"), root_2);
						adaptor.addChild(root_2, stream_r.nextNode());
						adaptor.addChild(root_1, root_2);
						}

						// src/edu/kit/iti/algover/parser/Dafny.g:215:38: ^( ARGS ( expressions )? )
						{
						DafnyTree root_2 = (DafnyTree)adaptor.nil();
						root_2 = (DafnyTree)adaptor.becomeRoot((DafnyTree)adaptor.create(ARGS, "ARGS"), root_2);
						// src/edu/kit/iti/algover/parser/Dafny.g:215:45: ( expressions )?
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
					// src/edu/kit/iti/algover/parser/Dafny.g:216:5: ids ':=' 'call' ID '(' ( expressions )? ')' ';'
					{
					pushFollow(FOLLOW_ids_in_statement1316);
					ids103=ids();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_ids.add(ids103.getTree());
					string_literal104=(Token)match(input,ASSIGN,FOLLOW_ASSIGN_in_statement1318); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_ASSIGN.add(string_literal104);

					string_literal105=(Token)match(input,CALL,FOLLOW_CALL_in_statement1320); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_CALL.add(string_literal105);

					ID106=(Token)match(input,ID,FOLLOW_ID_in_statement1322); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_ID.add(ID106);

					char_literal107=(Token)match(input,68,FOLLOW_68_in_statement1324); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_68.add(char_literal107);

					// src/edu/kit/iti/algover/parser/Dafny.g:216:28: ( expressions )?
					int alt21=2;
					int LA21_0 = input.LA(1);
					if ( (LA21_0==BLOCK_BEGIN||LA21_0==ID||LA21_0==LIT||LA21_0==MINUS||(LA21_0 >= NOT && LA21_0 <= NULL)||LA21_0==THIS||LA21_0==68||LA21_0==73) ) {
						alt21=1;
					}
					switch (alt21) {
						case 1 :
							// src/edu/kit/iti/algover/parser/Dafny.g:216:28: expressions
							{
							pushFollow(FOLLOW_expressions_in_statement1326);
							expressions108=expressions();
							state._fsp--;
							if (state.failed) return retval;
							if ( state.backtracking==0 ) stream_expressions.add(expressions108.getTree());
							}
							break;

					}

					char_literal109=(Token)match(input,69,FOLLOW_69_in_statement1329); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_69.add(char_literal109);

					char_literal110=(Token)match(input,72,FOLLOW_72_in_statement1331); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_72.add(char_literal110);

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

					root_0 = (DafnyTree)adaptor.nil();
					// 217:9: -> ^( 'call' ID ^( RESULTS ids ) ^( ARGS ( expressions )? ) )
					{
						// src/edu/kit/iti/algover/parser/Dafny.g:217:12: ^( 'call' ID ^( RESULTS ids ) ^( ARGS ( expressions )? ) )
						{
						DafnyTree root_1 = (DafnyTree)adaptor.nil();
						root_1 = (DafnyTree)adaptor.becomeRoot(stream_CALL.nextNode(), root_1);
						adaptor.addChild(root_1, stream_ID.nextNode());
						// src/edu/kit/iti/algover/parser/Dafny.g:217:24: ^( RESULTS ids )
						{
						DafnyTree root_2 = (DafnyTree)adaptor.nil();
						root_2 = (DafnyTree)adaptor.becomeRoot((DafnyTree)adaptor.create(RESULTS, "RESULTS"), root_2);
						adaptor.addChild(root_2, stream_ids.nextTree());
						adaptor.addChild(root_1, root_2);
						}

						// src/edu/kit/iti/algover/parser/Dafny.g:217:39: ^( ARGS ( expressions )? )
						{
						DafnyTree root_2 = (DafnyTree)adaptor.nil();
						root_2 = (DafnyTree)adaptor.becomeRoot((DafnyTree)adaptor.create(ARGS, "ARGS"), root_2);
						// src/edu/kit/iti/algover/parser/Dafny.g:217:46: ( expressions )?
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
					// src/edu/kit/iti/algover/parser/Dafny.g:218:5: ( label )? 'while' expression ( invariant )+ ( modifies )? decreases relaxedBlock
					{
					// src/edu/kit/iti/algover/parser/Dafny.g:218:5: ( label )?
					int alt22=2;
					int LA22_0 = input.LA(1);
					if ( (LA22_0==LABEL) ) {
						alt22=1;
					}
					switch (alt22) {
						case 1 :
							// src/edu/kit/iti/algover/parser/Dafny.g:218:5: label
							{
							pushFollow(FOLLOW_label_in_statement1366);
							label111=label();
							state._fsp--;
							if (state.failed) return retval;
							if ( state.backtracking==0 ) stream_label.add(label111.getTree());
							}
							break;

					}

					string_literal112=(Token)match(input,WHILE,FOLLOW_WHILE_in_statement1375); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_WHILE.add(string_literal112);

					pushFollow(FOLLOW_expression_in_statement1377);
					expression113=expression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_expression.add(expression113.getTree());
					// src/edu/kit/iti/algover/parser/Dafny.g:219:26: ( invariant )+
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
							// src/edu/kit/iti/algover/parser/Dafny.g:219:26: invariant
							{
							pushFollow(FOLLOW_invariant_in_statement1379);
							invariant114=invariant();
							state._fsp--;
							if (state.failed) return retval;
							if ( state.backtracking==0 ) stream_invariant.add(invariant114.getTree());
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

					// src/edu/kit/iti/algover/parser/Dafny.g:219:37: ( modifies )?
					int alt24=2;
					int LA24_0 = input.LA(1);
					if ( (LA24_0==MODIFIES) ) {
						alt24=1;
					}
					switch (alt24) {
						case 1 :
							// src/edu/kit/iti/algover/parser/Dafny.g:219:37: modifies
							{
							pushFollow(FOLLOW_modifies_in_statement1382);
							modifies115=modifies();
							state._fsp--;
							if (state.failed) return retval;
							if ( state.backtracking==0 ) stream_modifies.add(modifies115.getTree());
							}
							break;

					}

					pushFollow(FOLLOW_decreases_in_statement1385);
					decreases116=decreases();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_decreases.add(decreases116.getTree());
					pushFollow(FOLLOW_relaxedBlock_in_statement1387);
					relaxedBlock117=relaxedBlock();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_relaxedBlock.add(relaxedBlock117.getTree());
					// AST REWRITE
					// elements: relaxedBlock, WHILE, decreases, modifies, expression, invariant, label
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (DafnyTree)adaptor.nil();
					// 220:9: -> ^( 'while' ( label )? expression ( invariant )+ ( modifies )? decreases relaxedBlock )
					{
						// src/edu/kit/iti/algover/parser/Dafny.g:220:12: ^( 'while' ( label )? expression ( invariant )+ ( modifies )? decreases relaxedBlock )
						{
						DafnyTree root_1 = (DafnyTree)adaptor.nil();
						root_1 = (DafnyTree)adaptor.becomeRoot(stream_WHILE.nextNode(), root_1);
						// src/edu/kit/iti/algover/parser/Dafny.g:220:22: ( label )?
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

						// src/edu/kit/iti/algover/parser/Dafny.g:220:51: ( modifies )?
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
					// src/edu/kit/iti/algover/parser/Dafny.g:221:5: ( label )? 'if' ^ expression relaxedBlock ( options {greedy=true; } : 'else' ! relaxedBlock )?
					{
					root_0 = (DafnyTree)adaptor.nil();


					// src/edu/kit/iti/algover/parser/Dafny.g:221:5: ( label )?
					int alt25=2;
					int LA25_0 = input.LA(1);
					if ( (LA25_0==LABEL) ) {
						alt25=1;
					}
					switch (alt25) {
						case 1 :
							// src/edu/kit/iti/algover/parser/Dafny.g:221:5: label
							{
							pushFollow(FOLLOW_label_in_statement1422);
							label118=label();
							state._fsp--;
							if (state.failed) return retval;
							if ( state.backtracking==0 ) adaptor.addChild(root_0, label118.getTree());

							}
							break;

					}

					string_literal119=(Token)match(input,IF,FOLLOW_IF_in_statement1425); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					string_literal119_tree = (DafnyTree)adaptor.create(string_literal119);
					root_0 = (DafnyTree)adaptor.becomeRoot(string_literal119_tree, root_0);
					}

					pushFollow(FOLLOW_expression_in_statement1428);
					expression120=expression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, expression120.getTree());

					pushFollow(FOLLOW_relaxedBlock_in_statement1430);
					relaxedBlock121=relaxedBlock();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, relaxedBlock121.getTree());

					// src/edu/kit/iti/algover/parser/Dafny.g:222:7: ( options {greedy=true; } : 'else' ! relaxedBlock )?
					int alt26=2;
					int LA26_0 = input.LA(1);
					if ( (LA26_0==ELSE) ) {
						alt26=1;
					}
					switch (alt26) {
						case 1 :
							// src/edu/kit/iti/algover/parser/Dafny.g:222:36: 'else' ! relaxedBlock
							{
							string_literal122=(Token)match(input,ELSE,FOLLOW_ELSE_in_statement1451); if (state.failed) return retval;
							pushFollow(FOLLOW_relaxedBlock_in_statement1454);
							relaxedBlock123=relaxedBlock();
							state._fsp--;
							if (state.failed) return retval;
							if ( state.backtracking==0 ) adaptor.addChild(root_0, relaxedBlock123.getTree());

							}
							break;

					}

					}
					break;
				case 9 :
					// src/edu/kit/iti/algover/parser/Dafny.g:223:5: 'assert' ^ ( 'label' ! ID ':' !)? expression ';' !
					{
					root_0 = (DafnyTree)adaptor.nil();


					string_literal124=(Token)match(input,ASSERT,FOLLOW_ASSERT_in_statement1463); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					string_literal124_tree = (DafnyTree)adaptor.create(string_literal124);
					root_0 = (DafnyTree)adaptor.becomeRoot(string_literal124_tree, root_0);
					}

					// src/edu/kit/iti/algover/parser/Dafny.g:223:15: ( 'label' ! ID ':' !)?
					int alt27=2;
					int LA27_0 = input.LA(1);
					if ( (LA27_0==LABEL) ) {
						alt27=1;
					}
					switch (alt27) {
						case 1 :
							// src/edu/kit/iti/algover/parser/Dafny.g:223:17: 'label' ! ID ':' !
							{
							string_literal125=(Token)match(input,LABEL,FOLLOW_LABEL_in_statement1468); if (state.failed) return retval;
							ID126=(Token)match(input,ID,FOLLOW_ID_in_statement1471); if (state.failed) return retval;
							if ( state.backtracking==0 ) {
							ID126_tree = (DafnyTree)adaptor.create(ID126);
							adaptor.addChild(root_0, ID126_tree);
							}

							char_literal127=(Token)match(input,71,FOLLOW_71_in_statement1473); if (state.failed) return retval;
							}
							break;

					}

					pushFollow(FOLLOW_expression_in_statement1479);
					expression128=expression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, expression128.getTree());

					char_literal129=(Token)match(input,72,FOLLOW_72_in_statement1481); if (state.failed) return retval;
					}
					break;
				case 10 :
					// src/edu/kit/iti/algover/parser/Dafny.g:224:5: 'assume' ^ ( 'label' ! ID ':' !)? expression ';' !
					{
					root_0 = (DafnyTree)adaptor.nil();


					string_literal130=(Token)match(input,ASSUME,FOLLOW_ASSUME_in_statement1488); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					string_literal130_tree = (DafnyTree)adaptor.create(string_literal130);
					root_0 = (DafnyTree)adaptor.becomeRoot(string_literal130_tree, root_0);
					}

					// src/edu/kit/iti/algover/parser/Dafny.g:224:15: ( 'label' ! ID ':' !)?
					int alt28=2;
					int LA28_0 = input.LA(1);
					if ( (LA28_0==LABEL) ) {
						alt28=1;
					}
					switch (alt28) {
						case 1 :
							// src/edu/kit/iti/algover/parser/Dafny.g:224:17: 'label' ! ID ':' !
							{
							string_literal131=(Token)match(input,LABEL,FOLLOW_LABEL_in_statement1493); if (state.failed) return retval;
							ID132=(Token)match(input,ID,FOLLOW_ID_in_statement1496); if (state.failed) return retval;
							if ( state.backtracking==0 ) {
							ID132_tree = (DafnyTree)adaptor.create(ID132);
							adaptor.addChild(root_0, ID132_tree);
							}

							char_literal133=(Token)match(input,71,FOLLOW_71_in_statement1498); if (state.failed) return retval;
							}
							break;

					}

					pushFollow(FOLLOW_expression_in_statement1504);
					expression134=expression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, expression134.getTree());

					char_literal135=(Token)match(input,72,FOLLOW_72_in_statement1506); if (state.failed) return retval;
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
	// src/edu/kit/iti/algover/parser/Dafny.g:227:1: ids : ID ( ',' ! ID )+ ;
	public final DafnyParser.ids_return ids() throws RecognitionException {
		DafnyParser.ids_return retval = new DafnyParser.ids_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		Token ID136=null;
		Token char_literal137=null;
		Token ID138=null;

		DafnyTree ID136_tree=null;
		DafnyTree char_literal137_tree=null;
		DafnyTree ID138_tree=null;

		try {
			// src/edu/kit/iti/algover/parser/Dafny.g:227:4: ( ID ( ',' ! ID )+ )
			// src/edu/kit/iti/algover/parser/Dafny.g:228:3: ID ( ',' ! ID )+
			{
			root_0 = (DafnyTree)adaptor.nil();


			ID136=(Token)match(input,ID,FOLLOW_ID_in_ids1519); if (state.failed) return retval;
			if ( state.backtracking==0 ) {
			ID136_tree = (DafnyTree)adaptor.create(ID136);
			adaptor.addChild(root_0, ID136_tree);
			}

			// src/edu/kit/iti/algover/parser/Dafny.g:228:6: ( ',' ! ID )+
			int cnt30=0;
			loop30:
			while (true) {
				int alt30=2;
				int LA30_0 = input.LA(1);
				if ( (LA30_0==70) ) {
					alt30=1;
				}

				switch (alt30) {
				case 1 :
					// src/edu/kit/iti/algover/parser/Dafny.g:228:7: ',' ! ID
					{
					char_literal137=(Token)match(input,70,FOLLOW_70_in_ids1522); if (state.failed) return retval;
					ID138=(Token)match(input,ID,FOLLOW_ID_in_ids1525); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					ID138_tree = (DafnyTree)adaptor.create(ID138);
					adaptor.addChild(root_0, ID138_tree);
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
	// src/edu/kit/iti/algover/parser/Dafny.g:231:1: expressions : expression ( ',' ! expression )* ;
	public final DafnyParser.expressions_return expressions() throws RecognitionException {
		DafnyParser.expressions_return retval = new DafnyParser.expressions_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		Token char_literal140=null;
		ParserRuleReturnScope expression139 =null;
		ParserRuleReturnScope expression141 =null;

		DafnyTree char_literal140_tree=null;

		try {
			// src/edu/kit/iti/algover/parser/Dafny.g:231:12: ( expression ( ',' ! expression )* )
			// src/edu/kit/iti/algover/parser/Dafny.g:232:3: expression ( ',' ! expression )*
			{
			root_0 = (DafnyTree)adaptor.nil();


			pushFollow(FOLLOW_expression_in_expressions1539);
			expression139=expression();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, expression139.getTree());

			// src/edu/kit/iti/algover/parser/Dafny.g:232:14: ( ',' ! expression )*
			loop31:
			while (true) {
				int alt31=2;
				int LA31_0 = input.LA(1);
				if ( (LA31_0==70) ) {
					alt31=1;
				}

				switch (alt31) {
				case 1 :
					// src/edu/kit/iti/algover/parser/Dafny.g:232:16: ',' ! expression
					{
					char_literal140=(Token)match(input,70,FOLLOW_70_in_expressions1543); if (state.failed) return retval;
					pushFollow(FOLLOW_expression_in_expressions1546);
					expression141=expression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, expression141.getTree());

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
	// src/edu/kit/iti/algover/parser/Dafny.g:235:1: expression : or_expr ;
	public final DafnyParser.expression_return expression() throws RecognitionException {
		DafnyParser.expression_return retval = new DafnyParser.expression_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		ParserRuleReturnScope or_expr142 =null;


		try {
			// src/edu/kit/iti/algover/parser/Dafny.g:235:11: ( or_expr )
			// src/edu/kit/iti/algover/parser/Dafny.g:236:3: or_expr
			{
			root_0 = (DafnyTree)adaptor.nil();


			pushFollow(FOLLOW_or_expr_in_expression1561);
			or_expr142=or_expr();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, or_expr142.getTree());

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
	// src/edu/kit/iti/algover/parser/Dafny.g:238:1: or_expr : and_expr ( ( '||' ^| '==>' ^) or_expr )? ;
	public final DafnyParser.or_expr_return or_expr() throws RecognitionException {
		DafnyParser.or_expr_return retval = new DafnyParser.or_expr_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		Token string_literal144=null;
		Token string_literal145=null;
		ParserRuleReturnScope and_expr143 =null;
		ParserRuleReturnScope or_expr146 =null;

		DafnyTree string_literal144_tree=null;
		DafnyTree string_literal145_tree=null;

		try {
			// src/edu/kit/iti/algover/parser/Dafny.g:238:8: ( and_expr ( ( '||' ^| '==>' ^) or_expr )? )
			// src/edu/kit/iti/algover/parser/Dafny.g:239:3: and_expr ( ( '||' ^| '==>' ^) or_expr )?
			{
			root_0 = (DafnyTree)adaptor.nil();


			pushFollow(FOLLOW_and_expr_in_or_expr1570);
			and_expr143=and_expr();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, and_expr143.getTree());

			// src/edu/kit/iti/algover/parser/Dafny.g:239:12: ( ( '||' ^| '==>' ^) or_expr )?
			int alt33=2;
			int LA33_0 = input.LA(1);
			if ( (LA33_0==IMPLIES||LA33_0==OR) ) {
				alt33=1;
			}
			switch (alt33) {
				case 1 :
					// src/edu/kit/iti/algover/parser/Dafny.g:239:14: ( '||' ^| '==>' ^) or_expr
					{
					// src/edu/kit/iti/algover/parser/Dafny.g:239:14: ( '||' ^| '==>' ^)
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
							// src/edu/kit/iti/algover/parser/Dafny.g:239:15: '||' ^
							{
							string_literal144=(Token)match(input,OR,FOLLOW_OR_in_or_expr1575); if (state.failed) return retval;
							if ( state.backtracking==0 ) {
							string_literal144_tree = (DafnyTree)adaptor.create(string_literal144);
							root_0 = (DafnyTree)adaptor.becomeRoot(string_literal144_tree, root_0);
							}

							}
							break;
						case 2 :
							// src/edu/kit/iti/algover/parser/Dafny.g:239:23: '==>' ^
							{
							string_literal145=(Token)match(input,IMPLIES,FOLLOW_IMPLIES_in_or_expr1580); if (state.failed) return retval;
							if ( state.backtracking==0 ) {
							string_literal145_tree = (DafnyTree)adaptor.create(string_literal145);
							root_0 = (DafnyTree)adaptor.becomeRoot(string_literal145_tree, root_0);
							}

							}
							break;

					}

					pushFollow(FOLLOW_or_expr_in_or_expr1584);
					or_expr146=or_expr();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, or_expr146.getTree());

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
	// src/edu/kit/iti/algover/parser/Dafny.g:242:1: and_expr : rel_expr ( '&&' ^ and_expr )? ;
	public final DafnyParser.and_expr_return and_expr() throws RecognitionException {
		DafnyParser.and_expr_return retval = new DafnyParser.and_expr_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		Token string_literal148=null;
		ParserRuleReturnScope rel_expr147 =null;
		ParserRuleReturnScope and_expr149 =null;

		DafnyTree string_literal148_tree=null;

		try {
			// src/edu/kit/iti/algover/parser/Dafny.g:242:9: ( rel_expr ( '&&' ^ and_expr )? )
			// src/edu/kit/iti/algover/parser/Dafny.g:243:3: rel_expr ( '&&' ^ and_expr )?
			{
			root_0 = (DafnyTree)adaptor.nil();


			pushFollow(FOLLOW_rel_expr_in_and_expr1599);
			rel_expr147=rel_expr();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, rel_expr147.getTree());

			// src/edu/kit/iti/algover/parser/Dafny.g:243:12: ( '&&' ^ and_expr )?
			int alt34=2;
			int LA34_0 = input.LA(1);
			if ( (LA34_0==AND) ) {
				alt34=1;
			}
			switch (alt34) {
				case 1 :
					// src/edu/kit/iti/algover/parser/Dafny.g:243:14: '&&' ^ and_expr
					{
					string_literal148=(Token)match(input,AND,FOLLOW_AND_in_and_expr1603); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					string_literal148_tree = (DafnyTree)adaptor.create(string_literal148);
					root_0 = (DafnyTree)adaptor.becomeRoot(string_literal148_tree, root_0);
					}

					pushFollow(FOLLOW_and_expr_in_and_expr1606);
					and_expr149=and_expr();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, and_expr149.getTree());

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
	// src/edu/kit/iti/algover/parser/Dafny.g:246:1: rel_expr : add_expr ( ( '<' ^| '>' ^| '==' ^| '!=' ^| '<=' ^| '>=' ^) add_expr )? ;
	public final DafnyParser.rel_expr_return rel_expr() throws RecognitionException {
		DafnyParser.rel_expr_return retval = new DafnyParser.rel_expr_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		Token char_literal151=null;
		Token char_literal152=null;
		Token string_literal153=null;
		Token string_literal154=null;
		Token string_literal155=null;
		Token string_literal156=null;
		ParserRuleReturnScope add_expr150 =null;
		ParserRuleReturnScope add_expr157 =null;

		DafnyTree char_literal151_tree=null;
		DafnyTree char_literal152_tree=null;
		DafnyTree string_literal153_tree=null;
		DafnyTree string_literal154_tree=null;
		DafnyTree string_literal155_tree=null;
		DafnyTree string_literal156_tree=null;

		try {
			// src/edu/kit/iti/algover/parser/Dafny.g:246:9: ( add_expr ( ( '<' ^| '>' ^| '==' ^| '!=' ^| '<=' ^| '>=' ^) add_expr )? )
			// src/edu/kit/iti/algover/parser/Dafny.g:247:3: add_expr ( ( '<' ^| '>' ^| '==' ^| '!=' ^| '<=' ^| '>=' ^) add_expr )?
			{
			root_0 = (DafnyTree)adaptor.nil();


			pushFollow(FOLLOW_add_expr_in_rel_expr1621);
			add_expr150=add_expr();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, add_expr150.getTree());

			// src/edu/kit/iti/algover/parser/Dafny.g:247:12: ( ( '<' ^| '>' ^| '==' ^| '!=' ^| '<=' ^| '>=' ^) add_expr )?
			int alt36=2;
			int LA36_0 = input.LA(1);
			if ( (LA36_0==EQ||(LA36_0 >= GE && LA36_0 <= GT)||LA36_0==LE||LA36_0==LT||LA36_0==NEQ) ) {
				alt36=1;
			}
			switch (alt36) {
				case 1 :
					// src/edu/kit/iti/algover/parser/Dafny.g:247:14: ( '<' ^| '>' ^| '==' ^| '!=' ^| '<=' ^| '>=' ^) add_expr
					{
					// src/edu/kit/iti/algover/parser/Dafny.g:247:14: ( '<' ^| '>' ^| '==' ^| '!=' ^| '<=' ^| '>=' ^)
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
							// src/edu/kit/iti/algover/parser/Dafny.g:247:15: '<' ^
							{
							char_literal151=(Token)match(input,LT,FOLLOW_LT_in_rel_expr1626); if (state.failed) return retval;
							if ( state.backtracking==0 ) {
							char_literal151_tree = (DafnyTree)adaptor.create(char_literal151);
							root_0 = (DafnyTree)adaptor.becomeRoot(char_literal151_tree, root_0);
							}

							}
							break;
						case 2 :
							// src/edu/kit/iti/algover/parser/Dafny.g:247:22: '>' ^
							{
							char_literal152=(Token)match(input,GT,FOLLOW_GT_in_rel_expr1631); if (state.failed) return retval;
							if ( state.backtracking==0 ) {
							char_literal152_tree = (DafnyTree)adaptor.create(char_literal152);
							root_0 = (DafnyTree)adaptor.becomeRoot(char_literal152_tree, root_0);
							}

							}
							break;
						case 3 :
							// src/edu/kit/iti/algover/parser/Dafny.g:247:29: '==' ^
							{
							string_literal153=(Token)match(input,EQ,FOLLOW_EQ_in_rel_expr1636); if (state.failed) return retval;
							if ( state.backtracking==0 ) {
							string_literal153_tree = (DafnyTree)adaptor.create(string_literal153);
							root_0 = (DafnyTree)adaptor.becomeRoot(string_literal153_tree, root_0);
							}

							}
							break;
						case 4 :
							// src/edu/kit/iti/algover/parser/Dafny.g:247:37: '!=' ^
							{
							string_literal154=(Token)match(input,NEQ,FOLLOW_NEQ_in_rel_expr1641); if (state.failed) return retval;
							if ( state.backtracking==0 ) {
							string_literal154_tree = (DafnyTree)adaptor.create(string_literal154);
							root_0 = (DafnyTree)adaptor.becomeRoot(string_literal154_tree, root_0);
							}

							}
							break;
						case 5 :
							// src/edu/kit/iti/algover/parser/Dafny.g:247:45: '<=' ^
							{
							string_literal155=(Token)match(input,LE,FOLLOW_LE_in_rel_expr1646); if (state.failed) return retval;
							if ( state.backtracking==0 ) {
							string_literal155_tree = (DafnyTree)adaptor.create(string_literal155);
							root_0 = (DafnyTree)adaptor.becomeRoot(string_literal155_tree, root_0);
							}

							}
							break;
						case 6 :
							// src/edu/kit/iti/algover/parser/Dafny.g:247:53: '>=' ^
							{
							string_literal156=(Token)match(input,GE,FOLLOW_GE_in_rel_expr1651); if (state.failed) return retval;
							if ( state.backtracking==0 ) {
							string_literal156_tree = (DafnyTree)adaptor.create(string_literal156);
							root_0 = (DafnyTree)adaptor.becomeRoot(string_literal156_tree, root_0);
							}

							}
							break;

					}

					pushFollow(FOLLOW_add_expr_in_rel_expr1655);
					add_expr157=add_expr();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, add_expr157.getTree());

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
	// src/edu/kit/iti/algover/parser/Dafny.g:250:1: add_expr : mul_expr ( ( '+' | '-' | '++' ) ^ add_expr )? ;
	public final DafnyParser.add_expr_return add_expr() throws RecognitionException {
		DafnyParser.add_expr_return retval = new DafnyParser.add_expr_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		Token set159=null;
		ParserRuleReturnScope mul_expr158 =null;
		ParserRuleReturnScope add_expr160 =null;

		DafnyTree set159_tree=null;

		try {
			// src/edu/kit/iti/algover/parser/Dafny.g:250:9: ( mul_expr ( ( '+' | '-' | '++' ) ^ add_expr )? )
			// src/edu/kit/iti/algover/parser/Dafny.g:251:3: mul_expr ( ( '+' | '-' | '++' ) ^ add_expr )?
			{
			root_0 = (DafnyTree)adaptor.nil();


			pushFollow(FOLLOW_mul_expr_in_add_expr1670);
			mul_expr158=mul_expr();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, mul_expr158.getTree());

			// src/edu/kit/iti/algover/parser/Dafny.g:251:12: ( ( '+' | '-' | '++' ) ^ add_expr )?
			int alt37=2;
			int LA37_0 = input.LA(1);
			if ( (LA37_0==MINUS||LA37_0==PLUS||LA37_0==UNION) ) {
				alt37=1;
			}
			switch (alt37) {
				case 1 :
					// src/edu/kit/iti/algover/parser/Dafny.g:251:14: ( '+' | '-' | '++' ) ^ add_expr
					{
					set159=input.LT(1);
					set159=input.LT(1);
					if ( input.LA(1)==MINUS||input.LA(1)==PLUS||input.LA(1)==UNION ) {
						input.consume();
						if ( state.backtracking==0 ) root_0 = (DafnyTree)adaptor.becomeRoot((DafnyTree)adaptor.create(set159), root_0);
						state.errorRecovery=false;
						state.failed=false;
					}
					else {
						if (state.backtracking>0) {state.failed=true; return retval;}
						MismatchedSetException mse = new MismatchedSetException(null,input);
						throw mse;
					}
					pushFollow(FOLLOW_add_expr_in_add_expr1687);
					add_expr160=add_expr();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, add_expr160.getTree());

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
	// src/edu/kit/iti/algover/parser/Dafny.g:254:1: mul_expr : prefix_expr ( ( '*' | '**' ) ^ mul_expr )? ;
	public final DafnyParser.mul_expr_return mul_expr() throws RecognitionException {
		DafnyParser.mul_expr_return retval = new DafnyParser.mul_expr_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		Token set162=null;
		ParserRuleReturnScope prefix_expr161 =null;
		ParserRuleReturnScope mul_expr163 =null;

		DafnyTree set162_tree=null;

		try {
			// src/edu/kit/iti/algover/parser/Dafny.g:254:9: ( prefix_expr ( ( '*' | '**' ) ^ mul_expr )? )
			// src/edu/kit/iti/algover/parser/Dafny.g:255:3: prefix_expr ( ( '*' | '**' ) ^ mul_expr )?
			{
			root_0 = (DafnyTree)adaptor.nil();


			pushFollow(FOLLOW_prefix_expr_in_mul_expr1702);
			prefix_expr161=prefix_expr();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, prefix_expr161.getTree());

			// src/edu/kit/iti/algover/parser/Dafny.g:255:15: ( ( '*' | '**' ) ^ mul_expr )?
			int alt38=2;
			int LA38_0 = input.LA(1);
			if ( (LA38_0==INTERSECT||LA38_0==TIMES) ) {
				alt38=1;
			}
			switch (alt38) {
				case 1 :
					// src/edu/kit/iti/algover/parser/Dafny.g:255:17: ( '*' | '**' ) ^ mul_expr
					{
					set162=input.LT(1);
					set162=input.LT(1);
					if ( input.LA(1)==INTERSECT||input.LA(1)==TIMES ) {
						input.consume();
						if ( state.backtracking==0 ) root_0 = (DafnyTree)adaptor.becomeRoot((DafnyTree)adaptor.create(set162), root_0);
						state.errorRecovery=false;
						state.failed=false;
					}
					else {
						if (state.backtracking>0) {state.failed=true; return retval;}
						MismatchedSetException mse = new MismatchedSetException(null,input);
						throw mse;
					}
					pushFollow(FOLLOW_mul_expr_in_mul_expr1715);
					mul_expr163=mul_expr();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, mul_expr163.getTree());

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
	// src/edu/kit/iti/algover/parser/Dafny.g:258:1: prefix_expr : ( '-' ^ prefix_expr | '!' ^ prefix_expr | postfix_expr );
	public final DafnyParser.prefix_expr_return prefix_expr() throws RecognitionException {
		DafnyParser.prefix_expr_return retval = new DafnyParser.prefix_expr_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		Token char_literal164=null;
		Token char_literal166=null;
		ParserRuleReturnScope prefix_expr165 =null;
		ParserRuleReturnScope prefix_expr167 =null;
		ParserRuleReturnScope postfix_expr168 =null;

		DafnyTree char_literal164_tree=null;
		DafnyTree char_literal166_tree=null;

		try {
			// src/edu/kit/iti/algover/parser/Dafny.g:258:12: ( '-' ^ prefix_expr | '!' ^ prefix_expr | postfix_expr )
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
			case 68:
			case 73:
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
					// src/edu/kit/iti/algover/parser/Dafny.g:259:5: '-' ^ prefix_expr
					{
					root_0 = (DafnyTree)adaptor.nil();


					char_literal164=(Token)match(input,MINUS,FOLLOW_MINUS_in_prefix_expr1732); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					char_literal164_tree = (DafnyTree)adaptor.create(char_literal164);
					root_0 = (DafnyTree)adaptor.becomeRoot(char_literal164_tree, root_0);
					}

					pushFollow(FOLLOW_prefix_expr_in_prefix_expr1735);
					prefix_expr165=prefix_expr();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, prefix_expr165.getTree());

					}
					break;
				case 2 :
					// src/edu/kit/iti/algover/parser/Dafny.g:260:5: '!' ^ prefix_expr
					{
					root_0 = (DafnyTree)adaptor.nil();


					char_literal166=(Token)match(input,NOT,FOLLOW_NOT_in_prefix_expr1741); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					char_literal166_tree = (DafnyTree)adaptor.create(char_literal166);
					root_0 = (DafnyTree)adaptor.becomeRoot(char_literal166_tree, root_0);
					}

					pushFollow(FOLLOW_prefix_expr_in_prefix_expr1744);
					prefix_expr167=prefix_expr();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, prefix_expr167.getTree());

					}
					break;
				case 3 :
					// src/edu/kit/iti/algover/parser/Dafny.g:261:5: postfix_expr
					{
					root_0 = (DafnyTree)adaptor.nil();


					pushFollow(FOLLOW_postfix_expr_in_prefix_expr1750);
					postfix_expr168=postfix_expr();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, postfix_expr168.getTree());

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
	// src/edu/kit/iti/algover/parser/Dafny.g:264:1: postfix_expr : ( atom_expr -> atom_expr ) ( '[' expression ']' -> ^( ARRAY_ACCESS atom_expr expression ) | '.' LENGTH -> ^( LENGTH atom_expr ) | '.' ID '(' expressions ')' -> ^( OBJ_FUNC_CALL ID atom_expr expressions ) | '.' ID -> ^( FIELD_ACCESS atom_expr ID ) )* ;
	public final DafnyParser.postfix_expr_return postfix_expr() throws RecognitionException {
		DafnyParser.postfix_expr_return retval = new DafnyParser.postfix_expr_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		Token char_literal170=null;
		Token char_literal172=null;
		Token char_literal173=null;
		Token LENGTH174=null;
		Token char_literal175=null;
		Token ID176=null;
		Token char_literal177=null;
		Token char_literal179=null;
		Token char_literal180=null;
		Token ID181=null;
		ParserRuleReturnScope atom_expr169 =null;
		ParserRuleReturnScope expression171 =null;
		ParserRuleReturnScope expressions178 =null;

		DafnyTree char_literal170_tree=null;
		DafnyTree char_literal172_tree=null;
		DafnyTree char_literal173_tree=null;
		DafnyTree LENGTH174_tree=null;
		DafnyTree char_literal175_tree=null;
		DafnyTree ID176_tree=null;
		DafnyTree char_literal177_tree=null;
		DafnyTree char_literal179_tree=null;
		DafnyTree char_literal180_tree=null;
		DafnyTree ID181_tree=null;
		RewriteRuleTokenStream stream_68=new RewriteRuleTokenStream(adaptor,"token 68");
		RewriteRuleTokenStream stream_69=new RewriteRuleTokenStream(adaptor,"token 69");
		RewriteRuleTokenStream stream_LENGTH=new RewriteRuleTokenStream(adaptor,"token LENGTH");
		RewriteRuleTokenStream stream_DOT=new RewriteRuleTokenStream(adaptor,"token DOT");
		RewriteRuleTokenStream stream_ID=new RewriteRuleTokenStream(adaptor,"token ID");
		RewriteRuleTokenStream stream_73=new RewriteRuleTokenStream(adaptor,"token 73");
		RewriteRuleTokenStream stream_74=new RewriteRuleTokenStream(adaptor,"token 74");
		RewriteRuleSubtreeStream stream_expression=new RewriteRuleSubtreeStream(adaptor,"rule expression");
		RewriteRuleSubtreeStream stream_atom_expr=new RewriteRuleSubtreeStream(adaptor,"rule atom_expr");
		RewriteRuleSubtreeStream stream_expressions=new RewriteRuleSubtreeStream(adaptor,"rule expressions");

		try {
			// src/edu/kit/iti/algover/parser/Dafny.g:264:13: ( ( atom_expr -> atom_expr ) ( '[' expression ']' -> ^( ARRAY_ACCESS atom_expr expression ) | '.' LENGTH -> ^( LENGTH atom_expr ) | '.' ID '(' expressions ')' -> ^( OBJ_FUNC_CALL ID atom_expr expressions ) | '.' ID -> ^( FIELD_ACCESS atom_expr ID ) )* )
			// src/edu/kit/iti/algover/parser/Dafny.g:265:3: ( atom_expr -> atom_expr ) ( '[' expression ']' -> ^( ARRAY_ACCESS atom_expr expression ) | '.' LENGTH -> ^( LENGTH atom_expr ) | '.' ID '(' expressions ')' -> ^( OBJ_FUNC_CALL ID atom_expr expressions ) | '.' ID -> ^( FIELD_ACCESS atom_expr ID ) )*
			{
			// src/edu/kit/iti/algover/parser/Dafny.g:265:3: ( atom_expr -> atom_expr )
			// src/edu/kit/iti/algover/parser/Dafny.g:265:5: atom_expr
			{
			pushFollow(FOLLOW_atom_expr_in_postfix_expr1764);
			atom_expr169=atom_expr();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) stream_atom_expr.add(atom_expr169.getTree());
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
			// 265:15: -> atom_expr
			{
				adaptor.addChild(root_0, stream_atom_expr.nextTree());
			}


			retval.tree = root_0;
			}

			}

			// src/edu/kit/iti/algover/parser/Dafny.g:266:3: ( '[' expression ']' -> ^( ARRAY_ACCESS atom_expr expression ) | '.' LENGTH -> ^( LENGTH atom_expr ) | '.' ID '(' expressions ')' -> ^( OBJ_FUNC_CALL ID atom_expr expressions ) | '.' ID -> ^( FIELD_ACCESS atom_expr ID ) )*
			loop40:
			while (true) {
				int alt40=5;
				int LA40_0 = input.LA(1);
				if ( (LA40_0==73) ) {
					alt40=1;
				}
				else if ( (LA40_0==DOT) ) {
					int LA40_3 = input.LA(2);
					if ( (LA40_3==LENGTH) ) {
						alt40=2;
					}
					else if ( (LA40_3==ID) ) {
						int LA40_5 = input.LA(3);
						if ( (LA40_5==68) ) {
							alt40=3;
						}
						else if ( (LA40_5==EOF||LA40_5==AND||LA40_5==ASSERT||LA40_5==ASSUME||(LA40_5 >= BLOCK_BEGIN && LA40_5 <= BLOCK_END)||(LA40_5 >= DECREASES && LA40_5 <= DOT)||(LA40_5 >= ENSURES && LA40_5 <= EQ)||(LA40_5 >= GE && LA40_5 <= GT)||(LA40_5 >= ID && LA40_5 <= IMPLIES)||(LA40_5 >= INTERSECT && LA40_5 <= LE)||LA40_5==LT||(LA40_5 >= MINUS && LA40_5 <= MODIFIES)||LA40_5==NEQ||(LA40_5 >= OR && LA40_5 <= REQUIRES)||(LA40_5 >= TIMES && LA40_5 <= WHILE)||(LA40_5 >= 69 && LA40_5 <= 70)||(LA40_5 >= 72 && LA40_5 <= 74)) ) {
							alt40=4;
						}

					}

				}

				switch (alt40) {
				case 1 :
					// src/edu/kit/iti/algover/parser/Dafny.g:266:5: '[' expression ']'
					{
					char_literal170=(Token)match(input,73,FOLLOW_73_in_postfix_expr1776); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_73.add(char_literal170);

					pushFollow(FOLLOW_expression_in_postfix_expr1778);
					expression171=expression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_expression.add(expression171.getTree());
					char_literal172=(Token)match(input,74,FOLLOW_74_in_postfix_expr1780); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_74.add(char_literal172);

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
					// 266:24: -> ^( ARRAY_ACCESS atom_expr expression )
					{
						// src/edu/kit/iti/algover/parser/Dafny.g:266:27: ^( ARRAY_ACCESS atom_expr expression )
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
					// src/edu/kit/iti/algover/parser/Dafny.g:267:5: '.' LENGTH
					{
					char_literal173=(Token)match(input,DOT,FOLLOW_DOT_in_postfix_expr1798); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_DOT.add(char_literal173);

					LENGTH174=(Token)match(input,LENGTH,FOLLOW_LENGTH_in_postfix_expr1800); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_LENGTH.add(LENGTH174);

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
					// 267:16: -> ^( LENGTH atom_expr )
					{
						// src/edu/kit/iti/algover/parser/Dafny.g:267:19: ^( LENGTH atom_expr )
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
					// src/edu/kit/iti/algover/parser/Dafny.g:268:5: '.' ID '(' expressions ')'
					{
					char_literal175=(Token)match(input,DOT,FOLLOW_DOT_in_postfix_expr1816); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_DOT.add(char_literal175);

					ID176=(Token)match(input,ID,FOLLOW_ID_in_postfix_expr1818); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_ID.add(ID176);

					char_literal177=(Token)match(input,68,FOLLOW_68_in_postfix_expr1820); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_68.add(char_literal177);

					pushFollow(FOLLOW_expressions_in_postfix_expr1822);
					expressions178=expressions();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_expressions.add(expressions178.getTree());
					char_literal179=(Token)match(input,69,FOLLOW_69_in_postfix_expr1824); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_69.add(char_literal179);

					// AST REWRITE
					// elements: expressions, ID, atom_expr
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (DafnyTree)adaptor.nil();
					// 268:32: -> ^( OBJ_FUNC_CALL ID atom_expr expressions )
					{
						// src/edu/kit/iti/algover/parser/Dafny.g:268:35: ^( OBJ_FUNC_CALL ID atom_expr expressions )
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
					// src/edu/kit/iti/algover/parser/Dafny.g:269:5: '.' ID
					{
					char_literal180=(Token)match(input,DOT,FOLLOW_DOT_in_postfix_expr1844); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_DOT.add(char_literal180);

					ID181=(Token)match(input,ID,FOLLOW_ID_in_postfix_expr1846); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_ID.add(ID181);

					// AST REWRITE
					// elements: ID, atom_expr
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (DafnyTree)adaptor.nil();
					// 269:12: -> ^( FIELD_ACCESS atom_expr ID )
					{
						// src/edu/kit/iti/algover/parser/Dafny.g:269:15: ^( FIELD_ACCESS atom_expr ID )
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
	// src/edu/kit/iti/algover/parser/Dafny.g:273:1: expression_only : expression EOF -> expression ;
	public final DafnyParser.expression_only_return expression_only() throws RecognitionException {
		DafnyParser.expression_only_return retval = new DafnyParser.expression_only_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		Token EOF183=null;
		ParserRuleReturnScope expression182 =null;

		DafnyTree EOF183_tree=null;
		RewriteRuleTokenStream stream_EOF=new RewriteRuleTokenStream(adaptor,"token EOF");
		RewriteRuleSubtreeStream stream_expression=new RewriteRuleSubtreeStream(adaptor,"rule expression");

		try {
			// src/edu/kit/iti/algover/parser/Dafny.g:273:16: ( expression EOF -> expression )
			// src/edu/kit/iti/algover/parser/Dafny.g:274:3: expression EOF
			{
			pushFollow(FOLLOW_expression_in_expression_only1875);
			expression182=expression();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) stream_expression.add(expression182.getTree());
			EOF183=(Token)match(input,EOF,FOLLOW_EOF_in_expression_only1877); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_EOF.add(EOF183);

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
			// 274:18: -> expression
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
	// src/edu/kit/iti/algover/parser/Dafny.g:278:1: atom_expr : ( ID | ID '(' expressions ')' -> ^( FUNC_CALL ID expressions ) | LIT | 'this' | NULL | quantifier | '(' ! expression ')' !|open= '{' ( expressions )? '}' -> ^( SETEX[$open] ( expressions )? ) |open= '[' ( expressions )? ']' -> ^( LISTEX[$open] ( expressions )? ) );
	public final DafnyParser.atom_expr_return atom_expr() throws RecognitionException {
		DafnyParser.atom_expr_return retval = new DafnyParser.atom_expr_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		Token open=null;
		Token ID184=null;
		Token ID185=null;
		Token char_literal186=null;
		Token char_literal188=null;
		Token LIT189=null;
		Token string_literal190=null;
		Token NULL191=null;
		Token char_literal193=null;
		Token char_literal195=null;
		Token char_literal197=null;
		Token char_literal199=null;
		ParserRuleReturnScope expressions187 =null;
		ParserRuleReturnScope quantifier192 =null;
		ParserRuleReturnScope expression194 =null;
		ParserRuleReturnScope expressions196 =null;
		ParserRuleReturnScope expressions198 =null;

		DafnyTree open_tree=null;
		DafnyTree ID184_tree=null;
		DafnyTree ID185_tree=null;
		DafnyTree char_literal186_tree=null;
		DafnyTree char_literal188_tree=null;
		DafnyTree LIT189_tree=null;
		DafnyTree string_literal190_tree=null;
		DafnyTree NULL191_tree=null;
		DafnyTree char_literal193_tree=null;
		DafnyTree char_literal195_tree=null;
		DafnyTree char_literal197_tree=null;
		DafnyTree char_literal199_tree=null;
		RewriteRuleTokenStream stream_68=new RewriteRuleTokenStream(adaptor,"token 68");
		RewriteRuleTokenStream stream_69=new RewriteRuleTokenStream(adaptor,"token 69");
		RewriteRuleTokenStream stream_BLOCK_END=new RewriteRuleTokenStream(adaptor,"token BLOCK_END");
		RewriteRuleTokenStream stream_BLOCK_BEGIN=new RewriteRuleTokenStream(adaptor,"token BLOCK_BEGIN");
		RewriteRuleTokenStream stream_ID=new RewriteRuleTokenStream(adaptor,"token ID");
		RewriteRuleTokenStream stream_73=new RewriteRuleTokenStream(adaptor,"token 73");
		RewriteRuleTokenStream stream_74=new RewriteRuleTokenStream(adaptor,"token 74");
		RewriteRuleSubtreeStream stream_expressions=new RewriteRuleSubtreeStream(adaptor,"rule expressions");

		try {
			// src/edu/kit/iti/algover/parser/Dafny.g:278:10: ( ID | ID '(' expressions ')' -> ^( FUNC_CALL ID expressions ) | LIT | 'this' | NULL | quantifier | '(' ! expression ')' !|open= '{' ( expressions )? '}' -> ^( SETEX[$open] ( expressions )? ) |open= '[' ( expressions )? ']' -> ^( LISTEX[$open] ( expressions )? ) )
			int alt43=9;
			switch ( input.LA(1) ) {
			case ID:
				{
				int LA43_1 = input.LA(2);
				if ( (LA43_1==68) ) {
					alt43=2;
				}
				else if ( (LA43_1==EOF||LA43_1==AND||LA43_1==ASSERT||LA43_1==ASSUME||(LA43_1 >= BLOCK_BEGIN && LA43_1 <= BLOCK_END)||(LA43_1 >= DECREASES && LA43_1 <= DOT)||(LA43_1 >= ENSURES && LA43_1 <= EQ)||(LA43_1 >= GE && LA43_1 <= GT)||(LA43_1 >= ID && LA43_1 <= IMPLIES)||(LA43_1 >= INTERSECT && LA43_1 <= LE)||LA43_1==LT||(LA43_1 >= MINUS && LA43_1 <= MODIFIES)||LA43_1==NEQ||(LA43_1 >= OR && LA43_1 <= REQUIRES)||(LA43_1 >= TIMES && LA43_1 <= WHILE)||(LA43_1 >= 69 && LA43_1 <= 70)||(LA43_1 >= 72 && LA43_1 <= 74)) ) {
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
			case 68:
				{
				int LA43_5 = input.LA(2);
				if ( (LA43_5==ALL||LA43_5==EX) ) {
					alt43=6;
				}
				else if ( (LA43_5==BLOCK_BEGIN||LA43_5==ID||LA43_5==LIT||LA43_5==MINUS||(LA43_5 >= NOT && LA43_5 <= NULL)||LA43_5==THIS||LA43_5==68||LA43_5==73) ) {
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
			case 73:
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
					// src/edu/kit/iti/algover/parser/Dafny.g:279:5: ID
					{
					root_0 = (DafnyTree)adaptor.nil();


					ID184=(Token)match(input,ID,FOLLOW_ID_in_atom_expr1896); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					ID184_tree = (DafnyTree)adaptor.create(ID184);
					adaptor.addChild(root_0, ID184_tree);
					}

					}
					break;
				case 2 :
					// src/edu/kit/iti/algover/parser/Dafny.g:280:5: ID '(' expressions ')'
					{
					ID185=(Token)match(input,ID,FOLLOW_ID_in_atom_expr1902); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_ID.add(ID185);

					char_literal186=(Token)match(input,68,FOLLOW_68_in_atom_expr1904); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_68.add(char_literal186);

					pushFollow(FOLLOW_expressions_in_atom_expr1906);
					expressions187=expressions();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_expressions.add(expressions187.getTree());
					char_literal188=(Token)match(input,69,FOLLOW_69_in_atom_expr1908); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_69.add(char_literal188);

					// AST REWRITE
					// elements: ID, expressions
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (DafnyTree)adaptor.nil();
					// 280:28: -> ^( FUNC_CALL ID expressions )
					{
						// src/edu/kit/iti/algover/parser/Dafny.g:280:31: ^( FUNC_CALL ID expressions )
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
					// src/edu/kit/iti/algover/parser/Dafny.g:281:5: LIT
					{
					root_0 = (DafnyTree)adaptor.nil();


					LIT189=(Token)match(input,LIT,FOLLOW_LIT_in_atom_expr1924); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					LIT189_tree = (DafnyTree)adaptor.create(LIT189);
					adaptor.addChild(root_0, LIT189_tree);
					}

					}
					break;
				case 4 :
					// src/edu/kit/iti/algover/parser/Dafny.g:282:5: 'this'
					{
					root_0 = (DafnyTree)adaptor.nil();


					string_literal190=(Token)match(input,THIS,FOLLOW_THIS_in_atom_expr1930); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					string_literal190_tree = (DafnyTree)adaptor.create(string_literal190);
					adaptor.addChild(root_0, string_literal190_tree);
					}

					}
					break;
				case 5 :
					// src/edu/kit/iti/algover/parser/Dafny.g:283:5: NULL
					{
					root_0 = (DafnyTree)adaptor.nil();


					NULL191=(Token)match(input,NULL,FOLLOW_NULL_in_atom_expr1936); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					NULL191_tree = (DafnyTree)adaptor.create(NULL191);
					adaptor.addChild(root_0, NULL191_tree);
					}

					}
					break;
				case 6 :
					// src/edu/kit/iti/algover/parser/Dafny.g:284:5: quantifier
					{
					root_0 = (DafnyTree)adaptor.nil();


					pushFollow(FOLLOW_quantifier_in_atom_expr1942);
					quantifier192=quantifier();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, quantifier192.getTree());

					}
					break;
				case 7 :
					// src/edu/kit/iti/algover/parser/Dafny.g:285:5: '(' ! expression ')' !
					{
					root_0 = (DafnyTree)adaptor.nil();


					char_literal193=(Token)match(input,68,FOLLOW_68_in_atom_expr1948); if (state.failed) return retval;
					pushFollow(FOLLOW_expression_in_atom_expr1951);
					expression194=expression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, expression194.getTree());

					char_literal195=(Token)match(input,69,FOLLOW_69_in_atom_expr1953); if (state.failed) return retval;
					}
					break;
				case 8 :
					// src/edu/kit/iti/algover/parser/Dafny.g:286:5: open= '{' ( expressions )? '}'
					{
					open=(Token)match(input,BLOCK_BEGIN,FOLLOW_BLOCK_BEGIN_in_atom_expr1962); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_BLOCK_BEGIN.add(open);

					// src/edu/kit/iti/algover/parser/Dafny.g:286:14: ( expressions )?
					int alt41=2;
					int LA41_0 = input.LA(1);
					if ( (LA41_0==BLOCK_BEGIN||LA41_0==ID||LA41_0==LIT||LA41_0==MINUS||(LA41_0 >= NOT && LA41_0 <= NULL)||LA41_0==THIS||LA41_0==68||LA41_0==73) ) {
						alt41=1;
					}
					switch (alt41) {
						case 1 :
							// src/edu/kit/iti/algover/parser/Dafny.g:286:14: expressions
							{
							pushFollow(FOLLOW_expressions_in_atom_expr1964);
							expressions196=expressions();
							state._fsp--;
							if (state.failed) return retval;
							if ( state.backtracking==0 ) stream_expressions.add(expressions196.getTree());
							}
							break;

					}

					char_literal197=(Token)match(input,BLOCK_END,FOLLOW_BLOCK_END_in_atom_expr1967); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_BLOCK_END.add(char_literal197);

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
					// 286:31: -> ^( SETEX[$open] ( expressions )? )
					{
						// src/edu/kit/iti/algover/parser/Dafny.g:286:34: ^( SETEX[$open] ( expressions )? )
						{
						DafnyTree root_1 = (DafnyTree)adaptor.nil();
						root_1 = (DafnyTree)adaptor.becomeRoot((DafnyTree)adaptor.create(SETEX, open), root_1);
						// src/edu/kit/iti/algover/parser/Dafny.g:286:49: ( expressions )?
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
					// src/edu/kit/iti/algover/parser/Dafny.g:287:5: open= '[' ( expressions )? ']'
					{
					open=(Token)match(input,73,FOLLOW_73_in_atom_expr1985); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_73.add(open);

					// src/edu/kit/iti/algover/parser/Dafny.g:287:14: ( expressions )?
					int alt42=2;
					int LA42_0 = input.LA(1);
					if ( (LA42_0==BLOCK_BEGIN||LA42_0==ID||LA42_0==LIT||LA42_0==MINUS||(LA42_0 >= NOT && LA42_0 <= NULL)||LA42_0==THIS||LA42_0==68||LA42_0==73) ) {
						alt42=1;
					}
					switch (alt42) {
						case 1 :
							// src/edu/kit/iti/algover/parser/Dafny.g:287:14: expressions
							{
							pushFollow(FOLLOW_expressions_in_atom_expr1987);
							expressions198=expressions();
							state._fsp--;
							if (state.failed) return retval;
							if ( state.backtracking==0 ) stream_expressions.add(expressions198.getTree());
							}
							break;

					}

					char_literal199=(Token)match(input,74,FOLLOW_74_in_atom_expr1990); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_74.add(char_literal199);

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
					// 287:31: -> ^( LISTEX[$open] ( expressions )? )
					{
						// src/edu/kit/iti/algover/parser/Dafny.g:287:34: ^( LISTEX[$open] ( expressions )? )
						{
						DafnyTree root_1 = (DafnyTree)adaptor.nil();
						root_1 = (DafnyTree)adaptor.becomeRoot((DafnyTree)adaptor.create(LISTEX, open), root_1);
						// src/edu/kit/iti/algover/parser/Dafny.g:287:50: ( expressions )?
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
	// src/edu/kit/iti/algover/parser/Dafny.g:290:1: quantifier : '(' ! ( ALL ^| EX ^) ID ':' ! type '::' ! expression ')' !;
	public final DafnyParser.quantifier_return quantifier() throws RecognitionException {
		DafnyParser.quantifier_return retval = new DafnyParser.quantifier_return();
		retval.start = input.LT(1);

		DafnyTree root_0 = null;

		Token char_literal200=null;
		Token ALL201=null;
		Token EX202=null;
		Token ID203=null;
		Token char_literal204=null;
		Token string_literal206=null;
		Token char_literal208=null;
		ParserRuleReturnScope type205 =null;
		ParserRuleReturnScope expression207 =null;

		DafnyTree char_literal200_tree=null;
		DafnyTree ALL201_tree=null;
		DafnyTree EX202_tree=null;
		DafnyTree ID203_tree=null;
		DafnyTree char_literal204_tree=null;
		DafnyTree string_literal206_tree=null;
		DafnyTree char_literal208_tree=null;

		try {
			// src/edu/kit/iti/algover/parser/Dafny.g:290:11: ( '(' ! ( ALL ^| EX ^) ID ':' ! type '::' ! expression ')' !)
			// src/edu/kit/iti/algover/parser/Dafny.g:291:3: '(' ! ( ALL ^| EX ^) ID ':' ! type '::' ! expression ')' !
			{
			root_0 = (DafnyTree)adaptor.nil();


			char_literal200=(Token)match(input,68,FOLLOW_68_in_quantifier2012); if (state.failed) return retval;
			// src/edu/kit/iti/algover/parser/Dafny.g:291:8: ( ALL ^| EX ^)
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
					// src/edu/kit/iti/algover/parser/Dafny.g:291:9: ALL ^
					{
					ALL201=(Token)match(input,ALL,FOLLOW_ALL_in_quantifier2016); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					ALL201_tree = (DafnyTree)adaptor.create(ALL201);
					root_0 = (DafnyTree)adaptor.becomeRoot(ALL201_tree, root_0);
					}

					}
					break;
				case 2 :
					// src/edu/kit/iti/algover/parser/Dafny.g:291:16: EX ^
					{
					EX202=(Token)match(input,EX,FOLLOW_EX_in_quantifier2021); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					EX202_tree = (DafnyTree)adaptor.create(EX202);
					root_0 = (DafnyTree)adaptor.becomeRoot(EX202_tree, root_0);
					}

					}
					break;

			}

			ID203=(Token)match(input,ID,FOLLOW_ID_in_quantifier2025); if (state.failed) return retval;
			if ( state.backtracking==0 ) {
			ID203_tree = (DafnyTree)adaptor.create(ID203);
			adaptor.addChild(root_0, ID203_tree);
			}

			char_literal204=(Token)match(input,71,FOLLOW_71_in_quantifier2027); if (state.failed) return retval;
			pushFollow(FOLLOW_type_in_quantifier2030);
			type205=type();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, type205.getTree());

			string_literal206=(Token)match(input,DOUBLECOLON,FOLLOW_DOUBLECOLON_in_quantifier2032); if (state.failed) return retval;
			pushFollow(FOLLOW_expression_in_quantifier2035);
			expression207=expression();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, expression207.getTree());

			char_literal208=(Token)match(input,69,FOLLOW_69_in_quantifier2037); if (state.failed) return retval;
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
		// src/edu/kit/iti/algover/parser/Dafny.g:214:5: ( ID ':=' 'call' )
		// src/edu/kit/iti/algover/parser/Dafny.g:214:6: ID ':=' 'call'
		{
		match(input,ID,FOLLOW_ID_in_synpred1_Dafny1251); if (state.failed) return;

		match(input,ASSIGN,FOLLOW_ASSIGN_in_synpred1_Dafny1253); if (state.failed) return;

		match(input,CALL,FOLLOW_CALL_in_synpred1_Dafny1255); if (state.failed) return;

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



	public static final BitSet FOLLOW_LABEL_in_label597 = new BitSet(new long[]{0x0000000100000000L});
	public static final BitSet FOLLOW_ID_in_label600 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000080L});
	public static final BitSet FOLLOW_71_in_label602 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_method_in_program616 = new BitSet(new long[]{0x0000210008040002L});
	public static final BitSet FOLLOW_function_in_program620 = new BitSet(new long[]{0x0000210008040002L});
	public static final BitSet FOLLOW_clazz_in_program624 = new BitSet(new long[]{0x0000210008040002L});
	public static final BitSet FOLLOW_CLASS_in_clazz639 = new BitSet(new long[]{0x0000000100000000L});
	public static final BitSet FOLLOW_ID_in_clazz642 = new BitSet(new long[]{0x0000000000004000L});
	public static final BitSet FOLLOW_BLOCK_BEGIN_in_clazz644 = new BitSet(new long[]{0x0000210008000000L,0x0000000000000002L});
	public static final BitSet FOLLOW_method_in_clazz651 = new BitSet(new long[]{0x0000210008008000L,0x0000000000000002L});
	public static final BitSet FOLLOW_function_in_clazz655 = new BitSet(new long[]{0x0000210008008000L,0x0000000000000002L});
	public static final BitSet FOLLOW_field_in_clazz659 = new BitSet(new long[]{0x0000210008008000L,0x0000000000000002L});
	public static final BitSet FOLLOW_BLOCK_END_in_clazz665 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_METHOD_in_method683 = new BitSet(new long[]{0x0000000100000000L});
	public static final BitSet FOLLOW_LEMMA_in_method687 = new BitSet(new long[]{0x0000000100000000L});
	public static final BitSet FOLLOW_ID_in_method692 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000010L});
	public static final BitSet FOLLOW_68_in_method694 = new BitSet(new long[]{0x0000000100000000L,0x0000000000000020L});
	public static final BitSet FOLLOW_vars_in_method696 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000020L});
	public static final BitSet FOLLOW_69_in_method699 = new BitSet(new long[]{0x0280000000884000L});
	public static final BitSet FOLLOW_returns__in_method705 = new BitSet(new long[]{0x0080000000884000L});
	public static final BitSet FOLLOW_requires_in_method714 = new BitSet(new long[]{0x0080000000884000L});
	public static final BitSet FOLLOW_ensures_in_method723 = new BitSet(new long[]{0x0000000000884000L});
	public static final BitSet FOLLOW_decreases_in_method732 = new BitSet(new long[]{0x0000000000004000L});
	public static final BitSet FOLLOW_BLOCK_BEGIN_in_method739 = new BitSet(new long[]{0x0000004300009400L,0x0000000000000006L});
	public static final BitSet FOLLOW_statements_in_method741 = new BitSet(new long[]{0x0000000000008000L});
	public static final BitSet FOLLOW_BLOCK_END_in_method744 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_FUNCTION_in_function806 = new BitSet(new long[]{0x0000000100000000L});
	public static final BitSet FOLLOW_ID_in_function811 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000010L});
	public static final BitSet FOLLOW_68_in_function813 = new BitSet(new long[]{0x0000000100000000L,0x0000000000000020L});
	public static final BitSet FOLLOW_vars_in_function816 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000020L});
	public static final BitSet FOLLOW_69_in_function819 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000080L});
	public static final BitSet FOLLOW_71_in_function822 = new BitSet(new long[]{0x0400000800010080L});
	public static final BitSet FOLLOW_type_in_function825 = new BitSet(new long[]{0x0000000000004000L});
	public static final BitSet FOLLOW_BLOCK_BEGIN_in_function829 = new BitSet(new long[]{0x400C480100004000L,0x0000000000000210L});
	public static final BitSet FOLLOW_expression_in_function832 = new BitSet(new long[]{0x0000000000008000L});
	public static final BitSet FOLLOW_BLOCK_END_in_function834 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_VAR_in_field847 = new BitSet(new long[]{0x0000000100000000L});
	public static final BitSet FOLLOW_ID_in_field849 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000080L});
	public static final BitSet FOLLOW_71_in_field851 = new BitSet(new long[]{0x0400000800010080L});
	public static final BitSet FOLLOW_type_in_field853 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000100L});
	public static final BitSet FOLLOW_72_in_field855 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_var_in_vars867 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000040L});
	public static final BitSet FOLLOW_70_in_vars873 = new BitSet(new long[]{0x0000000100000000L});
	public static final BitSet FOLLOW_var_in_vars876 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000040L});
	public static final BitSet FOLLOW_ID_in_var891 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000080L});
	public static final BitSet FOLLOW_71_in_var893 = new BitSet(new long[]{0x0400000800010080L});
	public static final BitSet FOLLOW_type_in_var895 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_INT_in_type919 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_BOOL_in_type923 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_SET_in_type927 = new BitSet(new long[]{0x0000100000000000L});
	public static final BitSet FOLLOW_LT_in_type930 = new BitSet(new long[]{0x0000000800000000L});
	public static final BitSet FOLLOW_INT_in_type933 = new BitSet(new long[]{0x0000000040000000L});
	public static final BitSet FOLLOW_GT_in_type935 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_ARRAY_in_type942 = new BitSet(new long[]{0x0000100000000000L});
	public static final BitSet FOLLOW_LT_in_type945 = new BitSet(new long[]{0x0000000800000000L});
	public static final BitSet FOLLOW_INT_in_type948 = new BitSet(new long[]{0x0000000040000000L});
	public static final BitSet FOLLOW_GT_in_type950 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_RETURNS_in_returns_963 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000010L});
	public static final BitSet FOLLOW_68_in_returns_966 = new BitSet(new long[]{0x0000000100000000L});
	public static final BitSet FOLLOW_vars_in_returns_969 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000020L});
	public static final BitSet FOLLOW_69_in_returns_971 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_REQUIRES_in_requires984 = new BitSet(new long[]{0x400C484100004000L,0x0000000000000210L});
	public static final BitSet FOLLOW_label_in_requires987 = new BitSet(new long[]{0x400C480100004000L,0x0000000000000210L});
	public static final BitSet FOLLOW_expression_in_requires990 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_ENSURES_in_ensures1002 = new BitSet(new long[]{0x400C484100004000L,0x0000000000000210L});
	public static final BitSet FOLLOW_label_in_ensures1005 = new BitSet(new long[]{0x400C480100004000L,0x0000000000000210L});
	public static final BitSet FOLLOW_expression_in_ensures1008 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_DECREASES_in_decreases1020 = new BitSet(new long[]{0x400C480100004000L,0x0000000000000210L});
	public static final BitSet FOLLOW_expression_in_decreases1023 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_INVARIANT_in_invariant1035 = new BitSet(new long[]{0x400C484100004000L,0x0000000000000210L});
	public static final BitSet FOLLOW_label_in_invariant1038 = new BitSet(new long[]{0x400C480100004000L,0x0000000000000210L});
	public static final BitSet FOLLOW_expression_in_invariant1041 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_MODIFIES_in_modifies1053 = new BitSet(new long[]{0x400C480100004000L,0x0000000000000210L});
	public static final BitSet FOLLOW_expressions_in_modifies1056 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_BLOCK_BEGIN_in_block1068 = new BitSet(new long[]{0x0000004300009400L,0x0000000000000006L});
	public static final BitSet FOLLOW_statements_in_block1070 = new BitSet(new long[]{0x0000000000008000L});
	public static final BitSet FOLLOW_BLOCK_END_in_block1073 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_block_in_relaxedBlock1096 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_statement_in_relaxedBlock1102 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_statement_in_statements1124 = new BitSet(new long[]{0x0000004300001402L,0x0000000000000006L});
	public static final BitSet FOLLOW_VAR_in_statement1141 = new BitSet(new long[]{0x0000000100000000L});
	public static final BitSet FOLLOW_ID_in_statement1144 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000080L});
	public static final BitSet FOLLOW_71_in_statement1146 = new BitSet(new long[]{0x0400000800010080L});
	public static final BitSet FOLLOW_type_in_statement1149 = new BitSet(new long[]{0x0000000000000800L,0x0000000000000100L});
	public static final BitSet FOLLOW_ASSIGN_in_statement1152 = new BitSet(new long[]{0x400C480100004000L,0x0000000000000210L});
	public static final BitSet FOLLOW_expression_in_statement1155 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000100L});
	public static final BitSet FOLLOW_72_in_statement1159 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_ID_in_statement1166 = new BitSet(new long[]{0x0000000000000800L});
	public static final BitSet FOLLOW_ASSIGN_in_statement1170 = new BitSet(new long[]{0x8000000000000000L});
	public static final BitSet FOLLOW_TIMES_in_statement1172 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000100L});
	public static final BitSet FOLLOW_72_in_statement1174 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_ID_in_statement1189 = new BitSet(new long[]{0x0000000000000800L});
	public static final BitSet FOLLOW_ASSIGN_in_statement1191 = new BitSet(new long[]{0x400C480100004000L,0x0000000000000210L});
	public static final BitSet FOLLOW_expression_in_statement1194 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000100L});
	public static final BitSet FOLLOW_72_in_statement1196 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_ID_in_statement1203 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000200L});
	public static final BitSet FOLLOW_73_in_statement1205 = new BitSet(new long[]{0x400C480100004000L,0x0000000000000210L});
	public static final BitSet FOLLOW_expression_in_statement1209 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000400L});
	public static final BitSet FOLLOW_74_in_statement1211 = new BitSet(new long[]{0x0000000000000800L});
	public static final BitSet FOLLOW_ASSIGN_in_statement1215 = new BitSet(new long[]{0x400C480100004000L,0x0000000000000210L});
	public static final BitSet FOLLOW_expression_in_statement1219 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000100L});
	public static final BitSet FOLLOW_72_in_statement1221 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_ID_in_statement1262 = new BitSet(new long[]{0x0000000000000800L});
	public static final BitSet FOLLOW_ASSIGN_in_statement1264 = new BitSet(new long[]{0x0000000000020000L});
	public static final BitSet FOLLOW_CALL_in_statement1266 = new BitSet(new long[]{0x0000000100000000L});
	public static final BitSet FOLLOW_ID_in_statement1270 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000010L});
	public static final BitSet FOLLOW_68_in_statement1272 = new BitSet(new long[]{0x400C480100004000L,0x0000000000000230L});
	public static final BitSet FOLLOW_expressions_in_statement1274 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000020L});
	public static final BitSet FOLLOW_69_in_statement1277 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000100L});
	public static final BitSet FOLLOW_72_in_statement1279 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_ids_in_statement1316 = new BitSet(new long[]{0x0000000000000800L});
	public static final BitSet FOLLOW_ASSIGN_in_statement1318 = new BitSet(new long[]{0x0000000000020000L});
	public static final BitSet FOLLOW_CALL_in_statement1320 = new BitSet(new long[]{0x0000000100000000L});
	public static final BitSet FOLLOW_ID_in_statement1322 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000010L});
	public static final BitSet FOLLOW_68_in_statement1324 = new BitSet(new long[]{0x400C480100004000L,0x0000000000000230L});
	public static final BitSet FOLLOW_expressions_in_statement1326 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000020L});
	public static final BitSet FOLLOW_69_in_statement1329 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000100L});
	public static final BitSet FOLLOW_72_in_statement1331 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_label_in_statement1366 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000004L});
	public static final BitSet FOLLOW_WHILE_in_statement1375 = new BitSet(new long[]{0x400C480100004000L,0x0000000000000210L});
	public static final BitSet FOLLOW_expression_in_statement1377 = new BitSet(new long[]{0x0000002000000000L});
	public static final BitSet FOLLOW_invariant_in_statement1379 = new BitSet(new long[]{0x0000802000080000L});
	public static final BitSet FOLLOW_modifies_in_statement1382 = new BitSet(new long[]{0x0000000000080000L});
	public static final BitSet FOLLOW_decreases_in_statement1385 = new BitSet(new long[]{0x0000004300005400L,0x0000000000000006L});
	public static final BitSet FOLLOW_relaxedBlock_in_statement1387 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_label_in_statement1422 = new BitSet(new long[]{0x0000000200000000L});
	public static final BitSet FOLLOW_IF_in_statement1425 = new BitSet(new long[]{0x400C480100004000L,0x0000000000000210L});
	public static final BitSet FOLLOW_expression_in_statement1428 = new BitSet(new long[]{0x0000004300005400L,0x0000000000000006L});
	public static final BitSet FOLLOW_relaxedBlock_in_statement1430 = new BitSet(new long[]{0x0000000000400002L});
	public static final BitSet FOLLOW_ELSE_in_statement1451 = new BitSet(new long[]{0x0000004300005400L,0x0000000000000006L});
	public static final BitSet FOLLOW_relaxedBlock_in_statement1454 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_ASSERT_in_statement1463 = new BitSet(new long[]{0x400C484100004000L,0x0000000000000210L});
	public static final BitSet FOLLOW_LABEL_in_statement1468 = new BitSet(new long[]{0x0000000100000000L});
	public static final BitSet FOLLOW_ID_in_statement1471 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000080L});
	public static final BitSet FOLLOW_71_in_statement1473 = new BitSet(new long[]{0x400C480100004000L,0x0000000000000210L});
	public static final BitSet FOLLOW_expression_in_statement1479 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000100L});
	public static final BitSet FOLLOW_72_in_statement1481 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_ASSUME_in_statement1488 = new BitSet(new long[]{0x400C484100004000L,0x0000000000000210L});
	public static final BitSet FOLLOW_LABEL_in_statement1493 = new BitSet(new long[]{0x0000000100000000L});
	public static final BitSet FOLLOW_ID_in_statement1496 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000080L});
	public static final BitSet FOLLOW_71_in_statement1498 = new BitSet(new long[]{0x400C480100004000L,0x0000000000000210L});
	public static final BitSet FOLLOW_expression_in_statement1504 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000100L});
	public static final BitSet FOLLOW_72_in_statement1506 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_ID_in_ids1519 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000040L});
	public static final BitSet FOLLOW_70_in_ids1522 = new BitSet(new long[]{0x0000000100000000L});
	public static final BitSet FOLLOW_ID_in_ids1525 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000040L});
	public static final BitSet FOLLOW_expression_in_expressions1539 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000040L});
	public static final BitSet FOLLOW_70_in_expressions1543 = new BitSet(new long[]{0x400C480100004000L,0x0000000000000210L});
	public static final BitSet FOLLOW_expression_in_expressions1546 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000040L});
	public static final BitSet FOLLOW_or_expr_in_expression1561 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_and_expr_in_or_expr1570 = new BitSet(new long[]{0x0020000400000002L});
	public static final BitSet FOLLOW_OR_in_or_expr1575 = new BitSet(new long[]{0x400C480100004000L,0x0000000000000210L});
	public static final BitSet FOLLOW_IMPLIES_in_or_expr1580 = new BitSet(new long[]{0x400C480100004000L,0x0000000000000210L});
	public static final BitSet FOLLOW_or_expr_in_or_expr1584 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_rel_expr_in_and_expr1599 = new BitSet(new long[]{0x0000000000000022L});
	public static final BitSet FOLLOW_AND_in_and_expr1603 = new BitSet(new long[]{0x400C480100004000L,0x0000000000000210L});
	public static final BitSet FOLLOW_and_expr_in_and_expr1606 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_add_expr_in_rel_expr1621 = new BitSet(new long[]{0x0002108061000002L});
	public static final BitSet FOLLOW_LT_in_rel_expr1626 = new BitSet(new long[]{0x400C480100004000L,0x0000000000000210L});
	public static final BitSet FOLLOW_GT_in_rel_expr1631 = new BitSet(new long[]{0x400C480100004000L,0x0000000000000210L});
	public static final BitSet FOLLOW_EQ_in_rel_expr1636 = new BitSet(new long[]{0x400C480100004000L,0x0000000000000210L});
	public static final BitSet FOLLOW_NEQ_in_rel_expr1641 = new BitSet(new long[]{0x400C480100004000L,0x0000000000000210L});
	public static final BitSet FOLLOW_LE_in_rel_expr1646 = new BitSet(new long[]{0x400C480100004000L,0x0000000000000210L});
	public static final BitSet FOLLOW_GE_in_rel_expr1651 = new BitSet(new long[]{0x400C480100004000L,0x0000000000000210L});
	public static final BitSet FOLLOW_add_expr_in_rel_expr1655 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_mul_expr_in_add_expr1670 = new BitSet(new long[]{0x0040400000000002L,0x0000000000000001L});
	public static final BitSet FOLLOW_set_in_add_expr1674 = new BitSet(new long[]{0x400C480100004000L,0x0000000000000210L});
	public static final BitSet FOLLOW_add_expr_in_add_expr1687 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_prefix_expr_in_mul_expr1702 = new BitSet(new long[]{0x8000001000000002L});
	public static final BitSet FOLLOW_set_in_mul_expr1706 = new BitSet(new long[]{0x400C480100004000L,0x0000000000000210L});
	public static final BitSet FOLLOW_mul_expr_in_mul_expr1715 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_MINUS_in_prefix_expr1732 = new BitSet(new long[]{0x400C480100004000L,0x0000000000000210L});
	public static final BitSet FOLLOW_prefix_expr_in_prefix_expr1735 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_NOT_in_prefix_expr1741 = new BitSet(new long[]{0x400C480100004000L,0x0000000000000210L});
	public static final BitSet FOLLOW_prefix_expr_in_prefix_expr1744 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_postfix_expr_in_prefix_expr1750 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_atom_expr_in_postfix_expr1764 = new BitSet(new long[]{0x0000000000100002L,0x0000000000000200L});
	public static final BitSet FOLLOW_73_in_postfix_expr1776 = new BitSet(new long[]{0x400C480100004000L,0x0000000000000210L});
	public static final BitSet FOLLOW_expression_in_postfix_expr1778 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000400L});
	public static final BitSet FOLLOW_74_in_postfix_expr1780 = new BitSet(new long[]{0x0000000000100002L,0x0000000000000200L});
	public static final BitSet FOLLOW_DOT_in_postfix_expr1798 = new BitSet(new long[]{0x0000020000000000L});
	public static final BitSet FOLLOW_LENGTH_in_postfix_expr1800 = new BitSet(new long[]{0x0000000000100002L,0x0000000000000200L});
	public static final BitSet FOLLOW_DOT_in_postfix_expr1816 = new BitSet(new long[]{0x0000000100000000L});
	public static final BitSet FOLLOW_ID_in_postfix_expr1818 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000010L});
	public static final BitSet FOLLOW_68_in_postfix_expr1820 = new BitSet(new long[]{0x400C480100004000L,0x0000000000000210L});
	public static final BitSet FOLLOW_expressions_in_postfix_expr1822 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000020L});
	public static final BitSet FOLLOW_69_in_postfix_expr1824 = new BitSet(new long[]{0x0000000000100002L,0x0000000000000200L});
	public static final BitSet FOLLOW_DOT_in_postfix_expr1844 = new BitSet(new long[]{0x0000000100000000L});
	public static final BitSet FOLLOW_ID_in_postfix_expr1846 = new BitSet(new long[]{0x0000000000100002L,0x0000000000000200L});
	public static final BitSet FOLLOW_expression_in_expression_only1875 = new BitSet(new long[]{0x0000000000000000L});
	public static final BitSet FOLLOW_EOF_in_expression_only1877 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_ID_in_atom_expr1896 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_ID_in_atom_expr1902 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000010L});
	public static final BitSet FOLLOW_68_in_atom_expr1904 = new BitSet(new long[]{0x400C480100004000L,0x0000000000000210L});
	public static final BitSet FOLLOW_expressions_in_atom_expr1906 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000020L});
	public static final BitSet FOLLOW_69_in_atom_expr1908 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_LIT_in_atom_expr1924 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_THIS_in_atom_expr1930 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_NULL_in_atom_expr1936 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_quantifier_in_atom_expr1942 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_68_in_atom_expr1948 = new BitSet(new long[]{0x400C480100004000L,0x0000000000000210L});
	public static final BitSet FOLLOW_expression_in_atom_expr1951 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000020L});
	public static final BitSet FOLLOW_69_in_atom_expr1953 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_BLOCK_BEGIN_in_atom_expr1962 = new BitSet(new long[]{0x400C48010000C000L,0x0000000000000210L});
	public static final BitSet FOLLOW_expressions_in_atom_expr1964 = new BitSet(new long[]{0x0000000000008000L});
	public static final BitSet FOLLOW_BLOCK_END_in_atom_expr1967 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_73_in_atom_expr1985 = new BitSet(new long[]{0x400C480100004000L,0x0000000000000610L});
	public static final BitSet FOLLOW_expressions_in_atom_expr1987 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000400L});
	public static final BitSet FOLLOW_74_in_atom_expr1990 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_68_in_quantifier2012 = new BitSet(new long[]{0x0000000002000010L});
	public static final BitSet FOLLOW_ALL_in_quantifier2016 = new BitSet(new long[]{0x0000000100000000L});
	public static final BitSet FOLLOW_EX_in_quantifier2021 = new BitSet(new long[]{0x0000000100000000L});
	public static final BitSet FOLLOW_ID_in_quantifier2025 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000080L});
	public static final BitSet FOLLOW_71_in_quantifier2027 = new BitSet(new long[]{0x0400000800010080L});
	public static final BitSet FOLLOW_type_in_quantifier2030 = new BitSet(new long[]{0x0000000000200000L});
	public static final BitSet FOLLOW_DOUBLECOLON_in_quantifier2032 = new BitSet(new long[]{0x400C480100004000L,0x0000000000000210L});
	public static final BitSet FOLLOW_expression_in_quantifier2035 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000020L});
	public static final BitSet FOLLOW_69_in_quantifier2037 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_ID_in_synpred1_Dafny1251 = new BitSet(new long[]{0x0000000000000800L});
	public static final BitSet FOLLOW_ASSIGN_in_synpred1_Dafny1253 = new BitSet(new long[]{0x0000000000020000L});
	public static final BitSet FOLLOW_CALL_in_synpred1_Dafny1255 = new BitSet(new long[]{0x0000000000000002L});
}
