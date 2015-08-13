// $ANTLR 3.5.1 Pseudo.g 2015-08-13 11:03:40

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
		"ARRAY_ACCESS", "ASSIGN", "BLOCK", "CALL", "DECREASES", "ELSE", "ENSURES", 
		"EQ", "EX", "FUNCTION", "GE", "GT", "ID", "IF", "IMPLIES", "INT", "INTERSECT", 
		"INVARIANT", "LE", "LISTEX", "LIT", "LT", "MINUS", "NOT", "OR", "PLUS", 
		"REQUIRES", "RESULTS", "RETURNS", "SET", "SETEX", "THEN", "TIMES", "UNION", 
		"VAR", "WHILE", "WS", "'('", "')'", "','", "':'", "';'", "'['", "']'", 
		"'begin'", "'do'", "'end'", "'{'", "'}'"
	};
	public static final int EOF=-1;
	public static final int T__45=45;
	public static final int T__46=46;
	public static final int T__47=47;
	public static final int T__48=48;
	public static final int T__49=49;
	public static final int T__50=50;
	public static final int T__51=51;
	public static final int T__52=52;
	public static final int T__53=53;
	public static final int T__54=54;
	public static final int T__55=55;
	public static final int T__56=56;
	public static final int ALL=4;
	public static final int AND=5;
	public static final int ARGS=6;
	public static final int ARRAY=7;
	public static final int ARRAY_ACCESS=8;
	public static final int ASSIGN=9;
	public static final int BLOCK=10;
	public static final int CALL=11;
	public static final int DECREASES=12;
	public static final int ELSE=13;
	public static final int ENSURES=14;
	public static final int EQ=15;
	public static final int EX=16;
	public static final int FUNCTION=17;
	public static final int GE=18;
	public static final int GT=19;
	public static final int ID=20;
	public static final int IF=21;
	public static final int IMPLIES=22;
	public static final int INT=23;
	public static final int INTERSECT=24;
	public static final int INVARIANT=25;
	public static final int LE=26;
	public static final int LISTEX=27;
	public static final int LIT=28;
	public static final int LT=29;
	public static final int MINUS=30;
	public static final int NOT=31;
	public static final int OR=32;
	public static final int PLUS=33;
	public static final int REQUIRES=34;
	public static final int RESULTS=35;
	public static final int RETURNS=36;
	public static final int SET=37;
	public static final int SETEX=38;
	public static final int THEN=39;
	public static final int TIMES=40;
	public static final int UNION=41;
	public static final int VAR=42;
	public static final int WHILE=43;
	public static final int WS=44;

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


	public static class program_return extends ParserRuleReturnScope {
		PseudoTree tree;
		@Override
		public PseudoTree getTree() { return tree; }
	};


	// $ANTLR start "program"
	// Pseudo.g:64:1: program : ( function )+ ;
	public final PseudoParser.program_return program() throws RecognitionException {
		PseudoParser.program_return retval = new PseudoParser.program_return();
		retval.start = input.LT(1);

		PseudoTree root_0 = null;

		ParserRuleReturnScope function1 =null;


		try {
			// Pseudo.g:64:8: ( ( function )+ )
			// Pseudo.g:65:3: ( function )+
			{
			root_0 = (PseudoTree)adaptor.nil();


			// Pseudo.g:65:3: ( function )+
			int cnt1=0;
			loop1:
			while (true) {
				int alt1=2;
				int LA1_0 = input.LA(1);
				if ( (LA1_0==FUNCTION) ) {
					alt1=1;
				}

				switch (alt1) {
				case 1 :
					// Pseudo.g:65:3: function
					{
					pushFollow(FOLLOW_function_in_program325);
					function1=function();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, function1.getTree());

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
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
			retval.tree = (PseudoTree)adaptor.errorNode(input, retval.start, input.LT(-1), re);
		}
		finally {
			// do for sure before leaving
		}
		return retval;
	}
	// $ANTLR end "program"


	public static class function_return extends ParserRuleReturnScope {
		PseudoTree tree;
		@Override
		public PseudoTree getTree() { return tree; }
	};


	// $ANTLR start "function"
	// Pseudo.g:68:1: function : 'function' ID '(' ( vars )? ')' ( return_ )? ( requires )* ( ensures )* ( decreases )? ( decl )? block -> ^( 'function' ID ^( ARGS ( vars )? ) ( return_ )? ( requires )* ( ensures )* ( decreases )? ( decl )? block ) ;
	public final PseudoParser.function_return function() throws RecognitionException {
		PseudoParser.function_return retval = new PseudoParser.function_return();
		retval.start = input.LT(1);

		PseudoTree root_0 = null;

		Token string_literal2=null;
		Token ID3=null;
		Token char_literal4=null;
		Token char_literal6=null;
		ParserRuleReturnScope vars5 =null;
		ParserRuleReturnScope return_7 =null;
		ParserRuleReturnScope requires8 =null;
		ParserRuleReturnScope ensures9 =null;
		ParserRuleReturnScope decreases10 =null;
		ParserRuleReturnScope decl11 =null;
		ParserRuleReturnScope block12 =null;

		PseudoTree string_literal2_tree=null;
		PseudoTree ID3_tree=null;
		PseudoTree char_literal4_tree=null;
		PseudoTree char_literal6_tree=null;
		RewriteRuleTokenStream stream_FUNCTION=new RewriteRuleTokenStream(adaptor,"token FUNCTION");
		RewriteRuleTokenStream stream_45=new RewriteRuleTokenStream(adaptor,"token 45");
		RewriteRuleTokenStream stream_46=new RewriteRuleTokenStream(adaptor,"token 46");
		RewriteRuleTokenStream stream_ID=new RewriteRuleTokenStream(adaptor,"token ID");
		RewriteRuleSubtreeStream stream_ensures=new RewriteRuleSubtreeStream(adaptor,"rule ensures");
		RewriteRuleSubtreeStream stream_vars=new RewriteRuleSubtreeStream(adaptor,"rule vars");
		RewriteRuleSubtreeStream stream_return_=new RewriteRuleSubtreeStream(adaptor,"rule return_");
		RewriteRuleSubtreeStream stream_decreases=new RewriteRuleSubtreeStream(adaptor,"rule decreases");
		RewriteRuleSubtreeStream stream_block=new RewriteRuleSubtreeStream(adaptor,"rule block");
		RewriteRuleSubtreeStream stream_requires=new RewriteRuleSubtreeStream(adaptor,"rule requires");
		RewriteRuleSubtreeStream stream_decl=new RewriteRuleSubtreeStream(adaptor,"rule decl");

		try {
			// Pseudo.g:68:9: ( 'function' ID '(' ( vars )? ')' ( return_ )? ( requires )* ( ensures )* ( decreases )? ( decl )? block -> ^( 'function' ID ^( ARGS ( vars )? ) ( return_ )? ( requires )* ( ensures )* ( decreases )? ( decl )? block ) )
			// Pseudo.g:69:3: 'function' ID '(' ( vars )? ')' ( return_ )? ( requires )* ( ensures )* ( decreases )? ( decl )? block
			{
			string_literal2=(Token)match(input,FUNCTION,FOLLOW_FUNCTION_in_function339); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_FUNCTION.add(string_literal2);

			ID3=(Token)match(input,ID,FOLLOW_ID_in_function341); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_ID.add(ID3);

			char_literal4=(Token)match(input,45,FOLLOW_45_in_function343); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_45.add(char_literal4);

			// Pseudo.g:69:21: ( vars )?
			int alt2=2;
			int LA2_0 = input.LA(1);
			if ( (LA2_0==ID) ) {
				alt2=1;
			}
			switch (alt2) {
				case 1 :
					// Pseudo.g:69:21: vars
					{
					pushFollow(FOLLOW_vars_in_function345);
					vars5=vars();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_vars.add(vars5.getTree());
					}
					break;

			}

			char_literal6=(Token)match(input,46,FOLLOW_46_in_function348); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_46.add(char_literal6);

			// Pseudo.g:70:3: ( return_ )?
			int alt3=2;
			int LA3_0 = input.LA(1);
			if ( (LA3_0==RETURNS) ) {
				alt3=1;
			}
			switch (alt3) {
				case 1 :
					// Pseudo.g:70:5: return_
					{
					pushFollow(FOLLOW_return__in_function354);
					return_7=return_();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_return_.add(return_7.getTree());
					}
					break;

			}

			// Pseudo.g:71:3: ( requires )*
			loop4:
			while (true) {
				int alt4=2;
				int LA4_0 = input.LA(1);
				if ( (LA4_0==REQUIRES) ) {
					alt4=1;
				}

				switch (alt4) {
				case 1 :
					// Pseudo.g:71:5: requires
					{
					pushFollow(FOLLOW_requires_in_function363);
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

			// Pseudo.g:72:3: ( ensures )*
			loop5:
			while (true) {
				int alt5=2;
				int LA5_0 = input.LA(1);
				if ( (LA5_0==ENSURES) ) {
					alt5=1;
				}

				switch (alt5) {
				case 1 :
					// Pseudo.g:72:5: ensures
					{
					pushFollow(FOLLOW_ensures_in_function372);
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

			// Pseudo.g:73:3: ( decreases )?
			int alt6=2;
			int LA6_0 = input.LA(1);
			if ( (LA6_0==DECREASES) ) {
				alt6=1;
			}
			switch (alt6) {
				case 1 :
					// Pseudo.g:73:5: decreases
					{
					pushFollow(FOLLOW_decreases_in_function381);
					decreases10=decreases();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_decreases.add(decreases10.getTree());
					}
					break;

			}

			// Pseudo.g:74:3: ( decl )?
			int alt7=2;
			int LA7_0 = input.LA(1);
			if ( (LA7_0==VAR) ) {
				alt7=1;
			}
			switch (alt7) {
				case 1 :
					// Pseudo.g:74:5: decl
					{
					pushFollow(FOLLOW_decl_in_function390);
					decl11=decl();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_decl.add(decl11.getTree());
					}
					break;

			}

			pushFollow(FOLLOW_block_in_function397);
			block12=block();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) stream_block.add(block12.getTree());
			// AST REWRITE
			// elements: FUNCTION, block, return_, requires, decl, decreases, vars, ID, ensures
			// token labels: 
			// rule labels: retval
			// token list labels: 
			// rule list labels: 
			// wildcard labels: 
			if ( state.backtracking==0 ) {
			retval.tree = root_0;
			RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

			root_0 = (PseudoTree)adaptor.nil();
			// 76:3: -> ^( 'function' ID ^( ARGS ( vars )? ) ( return_ )? ( requires )* ( ensures )* ( decreases )? ( decl )? block )
			{
				// Pseudo.g:77:5: ^( 'function' ID ^( ARGS ( vars )? ) ( return_ )? ( requires )* ( ensures )* ( decreases )? ( decl )? block )
				{
				PseudoTree root_1 = (PseudoTree)adaptor.nil();
				root_1 = (PseudoTree)adaptor.becomeRoot(stream_FUNCTION.nextNode(), root_1);
				adaptor.addChild(root_1, stream_ID.nextNode());
				// Pseudo.g:77:21: ^( ARGS ( vars )? )
				{
				PseudoTree root_2 = (PseudoTree)adaptor.nil();
				root_2 = (PseudoTree)adaptor.becomeRoot((PseudoTree)adaptor.create(ARGS, "ARGS"), root_2);
				// Pseudo.g:77:28: ( vars )?
				if ( stream_vars.hasNext() ) {
					adaptor.addChild(root_2, stream_vars.nextTree());
				}
				stream_vars.reset();

				adaptor.addChild(root_1, root_2);
				}

				// Pseudo.g:77:35: ( return_ )?
				if ( stream_return_.hasNext() ) {
					adaptor.addChild(root_1, stream_return_.nextTree());
				}
				stream_return_.reset();

				// Pseudo.g:77:44: ( requires )*
				while ( stream_requires.hasNext() ) {
					adaptor.addChild(root_1, stream_requires.nextTree());
				}
				stream_requires.reset();

				// Pseudo.g:77:54: ( ensures )*
				while ( stream_ensures.hasNext() ) {
					adaptor.addChild(root_1, stream_ensures.nextTree());
				}
				stream_ensures.reset();

				// Pseudo.g:78:9: ( decreases )?
				if ( stream_decreases.hasNext() ) {
					adaptor.addChild(root_1, stream_decreases.nextTree());
				}
				stream_decreases.reset();

				// Pseudo.g:78:20: ( decl )?
				if ( stream_decl.hasNext() ) {
					adaptor.addChild(root_1, stream_decl.nextTree());
				}
				stream_decl.reset();

				adaptor.addChild(root_1, stream_block.nextTree());
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
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
			retval.tree = (PseudoTree)adaptor.errorNode(input, retval.start, input.LT(-1), re);
		}
		finally {
			// do for sure before leaving
		}
		return retval;
	}
	// $ANTLR end "function"


	public static class vars_return extends ParserRuleReturnScope {
		PseudoTree tree;
		@Override
		public PseudoTree getTree() { return tree; }
	};


	// $ANTLR start "vars"
	// Pseudo.g:81:1: vars : var ( ',' ! var )* ;
	public final PseudoParser.vars_return vars() throws RecognitionException {
		PseudoParser.vars_return retval = new PseudoParser.vars_return();
		retval.start = input.LT(1);

		PseudoTree root_0 = null;

		Token char_literal14=null;
		ParserRuleReturnScope var13 =null;
		ParserRuleReturnScope var15 =null;

		PseudoTree char_literal14_tree=null;

		try {
			// Pseudo.g:81:5: ( var ( ',' ! var )* )
			// Pseudo.g:82:3: var ( ',' ! var )*
			{
			root_0 = (PseudoTree)adaptor.nil();


			pushFollow(FOLLOW_var_in_vars456);
			var13=var();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, var13.getTree());

			// Pseudo.g:83:3: ( ',' ! var )*
			loop8:
			while (true) {
				int alt8=2;
				int LA8_0 = input.LA(1);
				if ( (LA8_0==47) ) {
					alt8=1;
				}

				switch (alt8) {
				case 1 :
					// Pseudo.g:83:5: ',' ! var
					{
					char_literal14=(Token)match(input,47,FOLLOW_47_in_vars462); if (state.failed) return retval;
					pushFollow(FOLLOW_var_in_vars465);
					var15=var();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, var15.getTree());

					}
					break;

				default :
					break loop8;
				}
			}

			}

			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (PseudoTree)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
			retval.tree = (PseudoTree)adaptor.errorNode(input, retval.start, input.LT(-1), re);
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
	// Pseudo.g:86:1: var : ID ':' type -> ^( VAR ID type ) ;
	public final PseudoParser.var_return var() throws RecognitionException {
		PseudoParser.var_return retval = new PseudoParser.var_return();
		retval.start = input.LT(1);

		PseudoTree root_0 = null;

		Token ID16=null;
		Token char_literal17=null;
		ParserRuleReturnScope type18 =null;

		PseudoTree ID16_tree=null;
		PseudoTree char_literal17_tree=null;
		RewriteRuleTokenStream stream_48=new RewriteRuleTokenStream(adaptor,"token 48");
		RewriteRuleTokenStream stream_ID=new RewriteRuleTokenStream(adaptor,"token ID");
		RewriteRuleSubtreeStream stream_type=new RewriteRuleSubtreeStream(adaptor,"rule type");

		try {
			// Pseudo.g:86:4: ( ID ':' type -> ^( VAR ID type ) )
			// Pseudo.g:87:3: ID ':' type
			{
			ID16=(Token)match(input,ID,FOLLOW_ID_in_var480); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_ID.add(ID16);

			char_literal17=(Token)match(input,48,FOLLOW_48_in_var482); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_48.add(char_literal17);

			pushFollow(FOLLOW_type_in_var484);
			type18=type();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) stream_type.add(type18.getTree());
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
			// 87:15: -> ^( VAR ID type )
			{
				// Pseudo.g:87:18: ^( VAR ID type )
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
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
			retval.tree = (PseudoTree)adaptor.errorNode(input, retval.start, input.LT(-1), re);
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
	// Pseudo.g:90:1: type : ( INT | SET | ARRAY );
	public final PseudoParser.type_return type() throws RecognitionException {
		PseudoParser.type_return retval = new PseudoParser.type_return();
		retval.start = input.LT(1);

		PseudoTree root_0 = null;

		Token set19=null;

		PseudoTree set19_tree=null;

		try {
			// Pseudo.g:90:5: ( INT | SET | ARRAY )
			// Pseudo.g:
			{
			root_0 = (PseudoTree)adaptor.nil();


			set19=input.LT(1);
			if ( input.LA(1)==ARRAY||input.LA(1)==INT||input.LA(1)==SET ) {
				input.consume();
				if ( state.backtracking==0 ) adaptor.addChild(root_0, (PseudoTree)adaptor.create(set19));
				state.errorRecovery=false;
				state.failed=false;
			}
			else {
				if (state.backtracking>0) {state.failed=true; return retval;}
				MismatchedSetException mse = new MismatchedSetException(null,input);
				throw mse;
			}
			}

			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (PseudoTree)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
			retval.tree = (PseudoTree)adaptor.errorNode(input, retval.start, input.LT(-1), re);
		}
		finally {
			// do for sure before leaving
		}
		return retval;
	}
	// $ANTLR end "type"


	public static class return__return extends ParserRuleReturnScope {
		PseudoTree tree;
		@Override
		public PseudoTree getTree() { return tree; }
	};


	// $ANTLR start "return_"
	// Pseudo.g:94:1: return_ : RETURNS ^ vars ;
	public final PseudoParser.return__return return_() throws RecognitionException {
		PseudoParser.return__return retval = new PseudoParser.return__return();
		retval.start = input.LT(1);

		PseudoTree root_0 = null;

		Token RETURNS20=null;
		ParserRuleReturnScope vars21 =null;

		PseudoTree RETURNS20_tree=null;

		try {
			// Pseudo.g:94:8: ( RETURNS ^ vars )
			// Pseudo.g:95:3: RETURNS ^ vars
			{
			root_0 = (PseudoTree)adaptor.nil();


			RETURNS20=(Token)match(input,RETURNS,FOLLOW_RETURNS_in_return_526); if (state.failed) return retval;
			if ( state.backtracking==0 ) {
			RETURNS20_tree = (PseudoTree)adaptor.create(RETURNS20);
			root_0 = (PseudoTree)adaptor.becomeRoot(RETURNS20_tree, root_0);
			}

			pushFollow(FOLLOW_vars_in_return_529);
			vars21=vars();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, vars21.getTree());

			}

			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (PseudoTree)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
			retval.tree = (PseudoTree)adaptor.errorNode(input, retval.start, input.LT(-1), re);
		}
		finally {
			// do for sure before leaving
		}
		return retval;
	}
	// $ANTLR end "return_"


	public static class requires_return extends ParserRuleReturnScope {
		PseudoTree tree;
		@Override
		public PseudoTree getTree() { return tree; }
	};


	// $ANTLR start "requires"
	// Pseudo.g:98:1: requires : REQUIRES ^ ( ID ':' !)? expression ;
	public final PseudoParser.requires_return requires() throws RecognitionException {
		PseudoParser.requires_return retval = new PseudoParser.requires_return();
		retval.start = input.LT(1);

		PseudoTree root_0 = null;

		Token REQUIRES22=null;
		Token ID23=null;
		Token char_literal24=null;
		ParserRuleReturnScope expression25 =null;

		PseudoTree REQUIRES22_tree=null;
		PseudoTree ID23_tree=null;
		PseudoTree char_literal24_tree=null;

		try {
			// Pseudo.g:98:9: ( REQUIRES ^ ( ID ':' !)? expression )
			// Pseudo.g:99:3: REQUIRES ^ ( ID ':' !)? expression
			{
			root_0 = (PseudoTree)adaptor.nil();


			REQUIRES22=(Token)match(input,REQUIRES,FOLLOW_REQUIRES_in_requires541); if (state.failed) return retval;
			if ( state.backtracking==0 ) {
			REQUIRES22_tree = (PseudoTree)adaptor.create(REQUIRES22);
			root_0 = (PseudoTree)adaptor.becomeRoot(REQUIRES22_tree, root_0);
			}

			// Pseudo.g:99:13: ( ID ':' !)?
			int alt9=2;
			int LA9_0 = input.LA(1);
			if ( (LA9_0==ID) ) {
				int LA9_1 = input.LA(2);
				if ( (LA9_1==48) ) {
					alt9=1;
				}
			}
			switch (alt9) {
				case 1 :
					// Pseudo.g:99:14: ID ':' !
					{
					ID23=(Token)match(input,ID,FOLLOW_ID_in_requires545); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					ID23_tree = (PseudoTree)adaptor.create(ID23);
					adaptor.addChild(root_0, ID23_tree);
					}

					char_literal24=(Token)match(input,48,FOLLOW_48_in_requires547); if (state.failed) return retval;
					}
					break;

			}

			pushFollow(FOLLOW_expression_in_requires552);
			expression25=expression();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, expression25.getTree());

			}

			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (PseudoTree)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
			retval.tree = (PseudoTree)adaptor.errorNode(input, retval.start, input.LT(-1), re);
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
	// Pseudo.g:102:1: ensures : ENSURES ^ ( ID ':' !)? expression ;
	public final PseudoParser.ensures_return ensures() throws RecognitionException {
		PseudoParser.ensures_return retval = new PseudoParser.ensures_return();
		retval.start = input.LT(1);

		PseudoTree root_0 = null;

		Token ENSURES26=null;
		Token ID27=null;
		Token char_literal28=null;
		ParserRuleReturnScope expression29 =null;

		PseudoTree ENSURES26_tree=null;
		PseudoTree ID27_tree=null;
		PseudoTree char_literal28_tree=null;

		try {
			// Pseudo.g:102:8: ( ENSURES ^ ( ID ':' !)? expression )
			// Pseudo.g:103:3: ENSURES ^ ( ID ':' !)? expression
			{
			root_0 = (PseudoTree)adaptor.nil();


			ENSURES26=(Token)match(input,ENSURES,FOLLOW_ENSURES_in_ensures564); if (state.failed) return retval;
			if ( state.backtracking==0 ) {
			ENSURES26_tree = (PseudoTree)adaptor.create(ENSURES26);
			root_0 = (PseudoTree)adaptor.becomeRoot(ENSURES26_tree, root_0);
			}

			// Pseudo.g:103:12: ( ID ':' !)?
			int alt10=2;
			int LA10_0 = input.LA(1);
			if ( (LA10_0==ID) ) {
				int LA10_1 = input.LA(2);
				if ( (LA10_1==48) ) {
					alt10=1;
				}
			}
			switch (alt10) {
				case 1 :
					// Pseudo.g:103:13: ID ':' !
					{
					ID27=(Token)match(input,ID,FOLLOW_ID_in_ensures568); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					ID27_tree = (PseudoTree)adaptor.create(ID27);
					adaptor.addChild(root_0, ID27_tree);
					}

					char_literal28=(Token)match(input,48,FOLLOW_48_in_ensures570); if (state.failed) return retval;
					}
					break;

			}

			pushFollow(FOLLOW_expression_in_ensures575);
			expression29=expression();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, expression29.getTree());

			}

			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (PseudoTree)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
			retval.tree = (PseudoTree)adaptor.errorNode(input, retval.start, input.LT(-1), re);
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
	// Pseudo.g:106:1: decreases : DECREASES ^ expression ;
	public final PseudoParser.decreases_return decreases() throws RecognitionException {
		PseudoParser.decreases_return retval = new PseudoParser.decreases_return();
		retval.start = input.LT(1);

		PseudoTree root_0 = null;

		Token DECREASES30=null;
		ParserRuleReturnScope expression31 =null;

		PseudoTree DECREASES30_tree=null;

		try {
			// Pseudo.g:106:10: ( DECREASES ^ expression )
			// Pseudo.g:107:3: DECREASES ^ expression
			{
			root_0 = (PseudoTree)adaptor.nil();


			DECREASES30=(Token)match(input,DECREASES,FOLLOW_DECREASES_in_decreases587); if (state.failed) return retval;
			if ( state.backtracking==0 ) {
			DECREASES30_tree = (PseudoTree)adaptor.create(DECREASES30);
			root_0 = (PseudoTree)adaptor.becomeRoot(DECREASES30_tree, root_0);
			}

			pushFollow(FOLLOW_expression_in_decreases590);
			expression31=expression();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, expression31.getTree());

			}

			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (PseudoTree)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
			retval.tree = (PseudoTree)adaptor.errorNode(input, retval.start, input.LT(-1), re);
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
	// Pseudo.g:110:1: invariant : INVARIANT ^ ( ID ':' !)? expression ;
	public final PseudoParser.invariant_return invariant() throws RecognitionException {
		PseudoParser.invariant_return retval = new PseudoParser.invariant_return();
		retval.start = input.LT(1);

		PseudoTree root_0 = null;

		Token INVARIANT32=null;
		Token ID33=null;
		Token char_literal34=null;
		ParserRuleReturnScope expression35 =null;

		PseudoTree INVARIANT32_tree=null;
		PseudoTree ID33_tree=null;
		PseudoTree char_literal34_tree=null;

		try {
			// Pseudo.g:110:10: ( INVARIANT ^ ( ID ':' !)? expression )
			// Pseudo.g:111:3: INVARIANT ^ ( ID ':' !)? expression
			{
			root_0 = (PseudoTree)adaptor.nil();


			INVARIANT32=(Token)match(input,INVARIANT,FOLLOW_INVARIANT_in_invariant602); if (state.failed) return retval;
			if ( state.backtracking==0 ) {
			INVARIANT32_tree = (PseudoTree)adaptor.create(INVARIANT32);
			root_0 = (PseudoTree)adaptor.becomeRoot(INVARIANT32_tree, root_0);
			}

			// Pseudo.g:111:14: ( ID ':' !)?
			int alt11=2;
			int LA11_0 = input.LA(1);
			if ( (LA11_0==ID) ) {
				int LA11_1 = input.LA(2);
				if ( (LA11_1==48) ) {
					alt11=1;
				}
			}
			switch (alt11) {
				case 1 :
					// Pseudo.g:111:15: ID ':' !
					{
					ID33=(Token)match(input,ID,FOLLOW_ID_in_invariant606); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					ID33_tree = (PseudoTree)adaptor.create(ID33);
					adaptor.addChild(root_0, ID33_tree);
					}

					char_literal34=(Token)match(input,48,FOLLOW_48_in_invariant608); if (state.failed) return retval;
					}
					break;

			}

			pushFollow(FOLLOW_expression_in_invariant613);
			expression35=expression();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, expression35.getTree());

			}

			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (PseudoTree)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
			retval.tree = (PseudoTree)adaptor.errorNode(input, retval.start, input.LT(-1), re);
		}
		finally {
			// do for sure before leaving
		}
		return retval;
	}
	// $ANTLR end "invariant"


	public static class decl_return extends ParserRuleReturnScope {
		PseudoTree tree;
		@Override
		public PseudoTree getTree() { return tree; }
	};


	// $ANTLR start "decl"
	// Pseudo.g:114:1: decl : VAR ^ vars ;
	public final PseudoParser.decl_return decl() throws RecognitionException {
		PseudoParser.decl_return retval = new PseudoParser.decl_return();
		retval.start = input.LT(1);

		PseudoTree root_0 = null;

		Token VAR36=null;
		ParserRuleReturnScope vars37 =null;

		PseudoTree VAR36_tree=null;

		try {
			// Pseudo.g:114:5: ( VAR ^ vars )
			// Pseudo.g:115:3: VAR ^ vars
			{
			root_0 = (PseudoTree)adaptor.nil();


			VAR36=(Token)match(input,VAR,FOLLOW_VAR_in_decl625); if (state.failed) return retval;
			if ( state.backtracking==0 ) {
			VAR36_tree = (PseudoTree)adaptor.create(VAR36);
			root_0 = (PseudoTree)adaptor.becomeRoot(VAR36_tree, root_0);
			}

			pushFollow(FOLLOW_vars_in_decl628);
			vars37=vars();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, vars37.getTree());

			}

			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (PseudoTree)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
			retval.tree = (PseudoTree)adaptor.errorNode(input, retval.start, input.LT(-1), re);
		}
		finally {
			// do for sure before leaving
		}
		return retval;
	}
	// $ANTLR end "decl"


	public static class block_return extends ParserRuleReturnScope {
		PseudoTree tree;
		@Override
		public PseudoTree getTree() { return tree; }
	};


	// $ANTLR start "block"
	// Pseudo.g:118:1: block : 'begin' statements 'end' -> ^( BLOCK statements ) ;
	public final PseudoParser.block_return block() throws RecognitionException {
		PseudoParser.block_return retval = new PseudoParser.block_return();
		retval.start = input.LT(1);

		PseudoTree root_0 = null;

		Token string_literal38=null;
		Token string_literal40=null;
		ParserRuleReturnScope statements39 =null;

		PseudoTree string_literal38_tree=null;
		PseudoTree string_literal40_tree=null;
		RewriteRuleTokenStream stream_52=new RewriteRuleTokenStream(adaptor,"token 52");
		RewriteRuleTokenStream stream_54=new RewriteRuleTokenStream(adaptor,"token 54");
		RewriteRuleSubtreeStream stream_statements=new RewriteRuleSubtreeStream(adaptor,"rule statements");

		try {
			// Pseudo.g:118:6: ( 'begin' statements 'end' -> ^( BLOCK statements ) )
			// Pseudo.g:119:3: 'begin' statements 'end'
			{
			string_literal38=(Token)match(input,52,FOLLOW_52_in_block640); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_52.add(string_literal38);

			pushFollow(FOLLOW_statements_in_block642);
			statements39=statements();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) stream_statements.add(statements39.getTree());
			string_literal40=(Token)match(input,54,FOLLOW_54_in_block644); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_54.add(string_literal40);

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
			// 119:28: -> ^( BLOCK statements )
			{
				// Pseudo.g:119:31: ^( BLOCK statements )
				{
				PseudoTree root_1 = (PseudoTree)adaptor.nil();
				root_1 = (PseudoTree)adaptor.becomeRoot((PseudoTree)adaptor.create(BLOCK, "BLOCK"), root_1);
				adaptor.addChild(root_1, stream_statements.nextTree());
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
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
			retval.tree = (PseudoTree)adaptor.errorNode(input, retval.start, input.LT(-1), re);
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
	// Pseudo.g:122:1: relaxedBlock : ( block | statement -> ^( BLOCK statement ) );
	public final PseudoParser.relaxedBlock_return relaxedBlock() throws RecognitionException {
		PseudoParser.relaxedBlock_return retval = new PseudoParser.relaxedBlock_return();
		retval.start = input.LT(1);

		PseudoTree root_0 = null;

		ParserRuleReturnScope block41 =null;
		ParserRuleReturnScope statement42 =null;

		RewriteRuleSubtreeStream stream_statement=new RewriteRuleSubtreeStream(adaptor,"rule statement");

		try {
			// Pseudo.g:122:13: ( block | statement -> ^( BLOCK statement ) )
			int alt12=2;
			int LA12_0 = input.LA(1);
			if ( (LA12_0==52) ) {
				alt12=1;
			}
			else if ( ((LA12_0 >= ID && LA12_0 <= IF)||LA12_0==WHILE) ) {
				alt12=2;
			}

			else {
				if (state.backtracking>0) {state.failed=true; return retval;}
				NoViableAltException nvae =
					new NoViableAltException("", 12, 0, input);
				throw nvae;
			}

			switch (alt12) {
				case 1 :
					// Pseudo.g:123:5: block
					{
					root_0 = (PseudoTree)adaptor.nil();


					pushFollow(FOLLOW_block_in_relaxedBlock666);
					block41=block();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, block41.getTree());

					}
					break;
				case 2 :
					// Pseudo.g:124:5: statement
					{
					pushFollow(FOLLOW_statement_in_relaxedBlock672);
					statement42=statement();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_statement.add(statement42.getTree());
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
					// 124:15: -> ^( BLOCK statement )
					{
						// Pseudo.g:124:18: ^( BLOCK statement )
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
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
			retval.tree = (PseudoTree)adaptor.errorNode(input, retval.start, input.LT(-1), re);
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
	// Pseudo.g:127:1: statements : statement ( ';' ! statement )* ;
	public final PseudoParser.statements_return statements() throws RecognitionException {
		PseudoParser.statements_return retval = new PseudoParser.statements_return();
		retval.start = input.LT(1);

		PseudoTree root_0 = null;

		Token char_literal44=null;
		ParserRuleReturnScope statement43 =null;
		ParserRuleReturnScope statement45 =null;

		PseudoTree char_literal44_tree=null;

		try {
			// Pseudo.g:127:11: ( statement ( ';' ! statement )* )
			// Pseudo.g:128:3: statement ( ';' ! statement )*
			{
			root_0 = (PseudoTree)adaptor.nil();


			pushFollow(FOLLOW_statement_in_statements692);
			statement43=statement();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, statement43.getTree());

			// Pseudo.g:128:13: ( ';' ! statement )*
			loop13:
			while (true) {
				int alt13=2;
				int LA13_0 = input.LA(1);
				if ( (LA13_0==49) ) {
					alt13=1;
				}

				switch (alt13) {
				case 1 :
					// Pseudo.g:128:15: ';' ! statement
					{
					char_literal44=(Token)match(input,49,FOLLOW_49_in_statements696); if (state.failed) return retval;
					pushFollow(FOLLOW_statement_in_statements699);
					statement45=statement();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, statement45.getTree());

					}
					break;

				default :
					break loop13;
				}
			}

			}

			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (PseudoTree)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
			retval.tree = (PseudoTree)adaptor.errorNode(input, retval.start, input.LT(-1), re);
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
	// Pseudo.g:131:1: statement : ( ID ':=' ^ expression | ( ID ':=' 'call' )=>r= ID ':=' 'call' f= ID '(' ( expressions )? ')' -> ^( 'call' $f ^( RESULTS $r) ^( ARGS ( expressions )? ) ) | ids ':=' 'call' ID '(' ( expressions )? ')' -> ^( 'call' ID ^( RESULTS ids ) ^( ARGS ( expressions )? ) ) | 'while' ^ expression ( invariant )+ decreases 'do' ! relaxedBlock | 'if' ^ expression 'then' ! relaxedBlock ( options {greedy=true; } : 'else' ! relaxedBlock )? );
	public final PseudoParser.statement_return statement() throws RecognitionException {
		PseudoParser.statement_return retval = new PseudoParser.statement_return();
		retval.start = input.LT(1);

		PseudoTree root_0 = null;

		Token r=null;
		Token f=null;
		Token ID46=null;
		Token string_literal47=null;
		Token string_literal49=null;
		Token string_literal50=null;
		Token char_literal51=null;
		Token char_literal53=null;
		Token string_literal55=null;
		Token string_literal56=null;
		Token ID57=null;
		Token char_literal58=null;
		Token char_literal60=null;
		Token string_literal61=null;
		Token string_literal65=null;
		Token string_literal67=null;
		Token string_literal69=null;
		Token string_literal71=null;
		ParserRuleReturnScope expression48 =null;
		ParserRuleReturnScope expressions52 =null;
		ParserRuleReturnScope ids54 =null;
		ParserRuleReturnScope expressions59 =null;
		ParserRuleReturnScope expression62 =null;
		ParserRuleReturnScope invariant63 =null;
		ParserRuleReturnScope decreases64 =null;
		ParserRuleReturnScope relaxedBlock66 =null;
		ParserRuleReturnScope expression68 =null;
		ParserRuleReturnScope relaxedBlock70 =null;
		ParserRuleReturnScope relaxedBlock72 =null;

		PseudoTree r_tree=null;
		PseudoTree f_tree=null;
		PseudoTree ID46_tree=null;
		PseudoTree string_literal47_tree=null;
		PseudoTree string_literal49_tree=null;
		PseudoTree string_literal50_tree=null;
		PseudoTree char_literal51_tree=null;
		PseudoTree char_literal53_tree=null;
		PseudoTree string_literal55_tree=null;
		PseudoTree string_literal56_tree=null;
		PseudoTree ID57_tree=null;
		PseudoTree char_literal58_tree=null;
		PseudoTree char_literal60_tree=null;
		PseudoTree string_literal61_tree=null;
		PseudoTree string_literal65_tree=null;
		PseudoTree string_literal67_tree=null;
		PseudoTree string_literal69_tree=null;
		PseudoTree string_literal71_tree=null;
		RewriteRuleTokenStream stream_45=new RewriteRuleTokenStream(adaptor,"token 45");
		RewriteRuleTokenStream stream_CALL=new RewriteRuleTokenStream(adaptor,"token CALL");
		RewriteRuleTokenStream stream_46=new RewriteRuleTokenStream(adaptor,"token 46");
		RewriteRuleTokenStream stream_ID=new RewriteRuleTokenStream(adaptor,"token ID");
		RewriteRuleTokenStream stream_ASSIGN=new RewriteRuleTokenStream(adaptor,"token ASSIGN");
		RewriteRuleSubtreeStream stream_ids=new RewriteRuleSubtreeStream(adaptor,"rule ids");
		RewriteRuleSubtreeStream stream_expressions=new RewriteRuleSubtreeStream(adaptor,"rule expressions");

		try {
			// Pseudo.g:131:10: ( ID ':=' ^ expression | ( ID ':=' 'call' )=>r= ID ':=' 'call' f= ID '(' ( expressions )? ')' -> ^( 'call' $f ^( RESULTS $r) ^( ARGS ( expressions )? ) ) | ids ':=' 'call' ID '(' ( expressions )? ')' -> ^( 'call' ID ^( RESULTS ids ) ^( ARGS ( expressions )? ) ) | 'while' ^ expression ( invariant )+ decreases 'do' ! relaxedBlock | 'if' ^ expression 'then' ! relaxedBlock ( options {greedy=true; } : 'else' ! relaxedBlock )? )
			int alt18=5;
			switch ( input.LA(1) ) {
			case ID:
				{
				int LA18_1 = input.LA(2);
				if ( (LA18_1==ASSIGN) ) {
					int LA18_4 = input.LA(3);
					if ( (LA18_4==CALL) && (synpred1_Pseudo())) {
						alt18=2;
					}
					else if ( (LA18_4==ID||LA18_4==LIT||(LA18_4 >= MINUS && LA18_4 <= NOT)||LA18_4==45||LA18_4==50||LA18_4==55) ) {
						alt18=1;
					}

					else {
						if (state.backtracking>0) {state.failed=true; return retval;}
						int nvaeMark = input.mark();
						try {
							for (int nvaeConsume = 0; nvaeConsume < 3 - 1; nvaeConsume++) {
								input.consume();
							}
							NoViableAltException nvae =
								new NoViableAltException("", 18, 4, input);
							throw nvae;
						} finally {
							input.rewind(nvaeMark);
						}
					}

				}
				else if ( (LA18_1==47) ) {
					alt18=3;
				}

				else {
					if (state.backtracking>0) {state.failed=true; return retval;}
					int nvaeMark = input.mark();
					try {
						input.consume();
						NoViableAltException nvae =
							new NoViableAltException("", 18, 1, input);
						throw nvae;
					} finally {
						input.rewind(nvaeMark);
					}
				}

				}
				break;
			case WHILE:
				{
				alt18=4;
				}
				break;
			case IF:
				{
				alt18=5;
				}
				break;
			default:
				if (state.backtracking>0) {state.failed=true; return retval;}
				NoViableAltException nvae =
					new NoViableAltException("", 18, 0, input);
				throw nvae;
			}
			switch (alt18) {
				case 1 :
					// Pseudo.g:132:5: ID ':=' ^ expression
					{
					root_0 = (PseudoTree)adaptor.nil();


					ID46=(Token)match(input,ID,FOLLOW_ID_in_statement716); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					ID46_tree = (PseudoTree)adaptor.create(ID46);
					adaptor.addChild(root_0, ID46_tree);
					}

					string_literal47=(Token)match(input,ASSIGN,FOLLOW_ASSIGN_in_statement718); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					string_literal47_tree = (PseudoTree)adaptor.create(string_literal47);
					root_0 = (PseudoTree)adaptor.becomeRoot(string_literal47_tree, root_0);
					}

					pushFollow(FOLLOW_expression_in_statement721);
					expression48=expression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, expression48.getTree());

					}
					break;
				case 2 :
					// Pseudo.g:133:5: ( ID ':=' 'call' )=>r= ID ':=' 'call' f= ID '(' ( expressions )? ')'
					{
					r=(Token)match(input,ID,FOLLOW_ID_in_statement739); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_ID.add(r);

					string_literal49=(Token)match(input,ASSIGN,FOLLOW_ASSIGN_in_statement741); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_ASSIGN.add(string_literal49);

					string_literal50=(Token)match(input,CALL,FOLLOW_CALL_in_statement743); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_CALL.add(string_literal50);

					f=(Token)match(input,ID,FOLLOW_ID_in_statement747); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_ID.add(f);

					char_literal51=(Token)match(input,45,FOLLOW_45_in_statement749); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_45.add(char_literal51);

					// Pseudo.g:133:51: ( expressions )?
					int alt14=2;
					int LA14_0 = input.LA(1);
					if ( (LA14_0==ID||LA14_0==LIT||(LA14_0 >= MINUS && LA14_0 <= NOT)||LA14_0==45||LA14_0==50||LA14_0==55) ) {
						alt14=1;
					}
					switch (alt14) {
						case 1 :
							// Pseudo.g:133:51: expressions
							{
							pushFollow(FOLLOW_expressions_in_statement751);
							expressions52=expressions();
							state._fsp--;
							if (state.failed) return retval;
							if ( state.backtracking==0 ) stream_expressions.add(expressions52.getTree());
							}
							break;

					}

					char_literal53=(Token)match(input,46,FOLLOW_46_in_statement754); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_46.add(char_literal53);

					// AST REWRITE
					// elements: r, expressions, f, CALL
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
					// 134:9: -> ^( 'call' $f ^( RESULTS $r) ^( ARGS ( expressions )? ) )
					{
						// Pseudo.g:134:12: ^( 'call' $f ^( RESULTS $r) ^( ARGS ( expressions )? ) )
						{
						PseudoTree root_1 = (PseudoTree)adaptor.nil();
						root_1 = (PseudoTree)adaptor.becomeRoot(stream_CALL.nextNode(), root_1);
						adaptor.addChild(root_1, stream_f.nextNode());
						// Pseudo.g:134:24: ^( RESULTS $r)
						{
						PseudoTree root_2 = (PseudoTree)adaptor.nil();
						root_2 = (PseudoTree)adaptor.becomeRoot((PseudoTree)adaptor.create(RESULTS, "RESULTS"), root_2);
						adaptor.addChild(root_2, stream_r.nextNode());
						adaptor.addChild(root_1, root_2);
						}

						// Pseudo.g:134:38: ^( ARGS ( expressions )? )
						{
						PseudoTree root_2 = (PseudoTree)adaptor.nil();
						root_2 = (PseudoTree)adaptor.becomeRoot((PseudoTree)adaptor.create(ARGS, "ARGS"), root_2);
						// Pseudo.g:134:45: ( expressions )?
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
					// Pseudo.g:135:5: ids ':=' 'call' ID '(' ( expressions )? ')'
					{
					pushFollow(FOLLOW_ids_in_statement791);
					ids54=ids();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_ids.add(ids54.getTree());
					string_literal55=(Token)match(input,ASSIGN,FOLLOW_ASSIGN_in_statement793); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_ASSIGN.add(string_literal55);

					string_literal56=(Token)match(input,CALL,FOLLOW_CALL_in_statement795); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_CALL.add(string_literal56);

					ID57=(Token)match(input,ID,FOLLOW_ID_in_statement797); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_ID.add(ID57);

					char_literal58=(Token)match(input,45,FOLLOW_45_in_statement799); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_45.add(char_literal58);

					// Pseudo.g:135:28: ( expressions )?
					int alt15=2;
					int LA15_0 = input.LA(1);
					if ( (LA15_0==ID||LA15_0==LIT||(LA15_0 >= MINUS && LA15_0 <= NOT)||LA15_0==45||LA15_0==50||LA15_0==55) ) {
						alt15=1;
					}
					switch (alt15) {
						case 1 :
							// Pseudo.g:135:28: expressions
							{
							pushFollow(FOLLOW_expressions_in_statement801);
							expressions59=expressions();
							state._fsp--;
							if (state.failed) return retval;
							if ( state.backtracking==0 ) stream_expressions.add(expressions59.getTree());
							}
							break;

					}

					char_literal60=(Token)match(input,46,FOLLOW_46_in_statement804); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_46.add(char_literal60);

					// AST REWRITE
					// elements: ID, expressions, ids, CALL
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (PseudoTree)adaptor.nil();
					// 136:9: -> ^( 'call' ID ^( RESULTS ids ) ^( ARGS ( expressions )? ) )
					{
						// Pseudo.g:136:12: ^( 'call' ID ^( RESULTS ids ) ^( ARGS ( expressions )? ) )
						{
						PseudoTree root_1 = (PseudoTree)adaptor.nil();
						root_1 = (PseudoTree)adaptor.becomeRoot(stream_CALL.nextNode(), root_1);
						adaptor.addChild(root_1, stream_ID.nextNode());
						// Pseudo.g:136:24: ^( RESULTS ids )
						{
						PseudoTree root_2 = (PseudoTree)adaptor.nil();
						root_2 = (PseudoTree)adaptor.becomeRoot((PseudoTree)adaptor.create(RESULTS, "RESULTS"), root_2);
						adaptor.addChild(root_2, stream_ids.nextTree());
						adaptor.addChild(root_1, root_2);
						}

						// Pseudo.g:136:39: ^( ARGS ( expressions )? )
						{
						PseudoTree root_2 = (PseudoTree)adaptor.nil();
						root_2 = (PseudoTree)adaptor.becomeRoot((PseudoTree)adaptor.create(ARGS, "ARGS"), root_2);
						// Pseudo.g:136:46: ( expressions )?
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
					// Pseudo.g:137:5: 'while' ^ expression ( invariant )+ decreases 'do' ! relaxedBlock
					{
					root_0 = (PseudoTree)adaptor.nil();


					string_literal61=(Token)match(input,WHILE,FOLLOW_WHILE_in_statement839); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					string_literal61_tree = (PseudoTree)adaptor.create(string_literal61);
					root_0 = (PseudoTree)adaptor.becomeRoot(string_literal61_tree, root_0);
					}

					pushFollow(FOLLOW_expression_in_statement842);
					expression62=expression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, expression62.getTree());

					// Pseudo.g:138:7: ( invariant )+
					int cnt16=0;
					loop16:
					while (true) {
						int alt16=2;
						int LA16_0 = input.LA(1);
						if ( (LA16_0==INVARIANT) ) {
							alt16=1;
						}

						switch (alt16) {
						case 1 :
							// Pseudo.g:138:7: invariant
							{
							pushFollow(FOLLOW_invariant_in_statement850);
							invariant63=invariant();
							state._fsp--;
							if (state.failed) return retval;
							if ( state.backtracking==0 ) adaptor.addChild(root_0, invariant63.getTree());

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

					pushFollow(FOLLOW_decreases_in_statement859);
					decreases64=decreases();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, decreases64.getTree());

					string_literal65=(Token)match(input,53,FOLLOW_53_in_statement867); if (state.failed) return retval;
					pushFollow(FOLLOW_relaxedBlock_in_statement870);
					relaxedBlock66=relaxedBlock();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, relaxedBlock66.getTree());

					}
					break;
				case 5 :
					// Pseudo.g:141:5: 'if' ^ expression 'then' ! relaxedBlock ( options {greedy=true; } : 'else' ! relaxedBlock )?
					{
					root_0 = (PseudoTree)adaptor.nil();


					string_literal67=(Token)match(input,IF,FOLLOW_IF_in_statement876); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					string_literal67_tree = (PseudoTree)adaptor.create(string_literal67);
					root_0 = (PseudoTree)adaptor.becomeRoot(string_literal67_tree, root_0);
					}

					pushFollow(FOLLOW_expression_in_statement879);
					expression68=expression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, expression68.getTree());

					string_literal69=(Token)match(input,THEN,FOLLOW_THEN_in_statement881); if (state.failed) return retval;
					pushFollow(FOLLOW_relaxedBlock_in_statement884);
					relaxedBlock70=relaxedBlock();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, relaxedBlock70.getTree());

					// Pseudo.g:142:7: ( options {greedy=true; } : 'else' ! relaxedBlock )?
					int alt17=2;
					int LA17_0 = input.LA(1);
					if ( (LA17_0==ELSE) ) {
						alt17=1;
					}
					switch (alt17) {
						case 1 :
							// Pseudo.g:142:36: 'else' ! relaxedBlock
							{
							string_literal71=(Token)match(input,ELSE,FOLLOW_ELSE_in_statement905); if (state.failed) return retval;
							pushFollow(FOLLOW_relaxedBlock_in_statement908);
							relaxedBlock72=relaxedBlock();
							state._fsp--;
							if (state.failed) return retval;
							if ( state.backtracking==0 ) adaptor.addChild(root_0, relaxedBlock72.getTree());

							}
							break;

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
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
			retval.tree = (PseudoTree)adaptor.errorNode(input, retval.start, input.LT(-1), re);
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
	// Pseudo.g:145:1: ids : ID ( ',' ! ID )+ ;
	public final PseudoParser.ids_return ids() throws RecognitionException {
		PseudoParser.ids_return retval = new PseudoParser.ids_return();
		retval.start = input.LT(1);

		PseudoTree root_0 = null;

		Token ID73=null;
		Token char_literal74=null;
		Token ID75=null;

		PseudoTree ID73_tree=null;
		PseudoTree char_literal74_tree=null;
		PseudoTree ID75_tree=null;

		try {
			// Pseudo.g:145:4: ( ID ( ',' ! ID )+ )
			// Pseudo.g:146:3: ID ( ',' ! ID )+
			{
			root_0 = (PseudoTree)adaptor.nil();


			ID73=(Token)match(input,ID,FOLLOW_ID_in_ids923); if (state.failed) return retval;
			if ( state.backtracking==0 ) {
			ID73_tree = (PseudoTree)adaptor.create(ID73);
			adaptor.addChild(root_0, ID73_tree);
			}

			// Pseudo.g:146:6: ( ',' ! ID )+
			int cnt19=0;
			loop19:
			while (true) {
				int alt19=2;
				int LA19_0 = input.LA(1);
				if ( (LA19_0==47) ) {
					alt19=1;
				}

				switch (alt19) {
				case 1 :
					// Pseudo.g:146:7: ',' ! ID
					{
					char_literal74=(Token)match(input,47,FOLLOW_47_in_ids926); if (state.failed) return retval;
					ID75=(Token)match(input,ID,FOLLOW_ID_in_ids929); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					ID75_tree = (PseudoTree)adaptor.create(ID75);
					adaptor.addChild(root_0, ID75_tree);
					}

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

			}

			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (PseudoTree)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
			retval.tree = (PseudoTree)adaptor.errorNode(input, retval.start, input.LT(-1), re);
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
	// Pseudo.g:149:1: expressions : expression ( ',' ! expression )* ;
	public final PseudoParser.expressions_return expressions() throws RecognitionException {
		PseudoParser.expressions_return retval = new PseudoParser.expressions_return();
		retval.start = input.LT(1);

		PseudoTree root_0 = null;

		Token char_literal77=null;
		ParserRuleReturnScope expression76 =null;
		ParserRuleReturnScope expression78 =null;

		PseudoTree char_literal77_tree=null;

		try {
			// Pseudo.g:149:12: ( expression ( ',' ! expression )* )
			// Pseudo.g:150:3: expression ( ',' ! expression )*
			{
			root_0 = (PseudoTree)adaptor.nil();


			pushFollow(FOLLOW_expression_in_expressions943);
			expression76=expression();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, expression76.getTree());

			// Pseudo.g:150:14: ( ',' ! expression )*
			loop20:
			while (true) {
				int alt20=2;
				int LA20_0 = input.LA(1);
				if ( (LA20_0==47) ) {
					alt20=1;
				}

				switch (alt20) {
				case 1 :
					// Pseudo.g:150:16: ',' ! expression
					{
					char_literal77=(Token)match(input,47,FOLLOW_47_in_expressions947); if (state.failed) return retval;
					pushFollow(FOLLOW_expression_in_expressions950);
					expression78=expression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, expression78.getTree());

					}
					break;

				default :
					break loop20;
				}
			}

			}

			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (PseudoTree)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
			retval.tree = (PseudoTree)adaptor.errorNode(input, retval.start, input.LT(-1), re);
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
	// Pseudo.g:153:1: expression : or_expr ;
	public final PseudoParser.expression_return expression() throws RecognitionException {
		PseudoParser.expression_return retval = new PseudoParser.expression_return();
		retval.start = input.LT(1);

		PseudoTree root_0 = null;

		ParserRuleReturnScope or_expr79 =null;


		try {
			// Pseudo.g:153:11: ( or_expr )
			// Pseudo.g:154:3: or_expr
			{
			root_0 = (PseudoTree)adaptor.nil();


			pushFollow(FOLLOW_or_expr_in_expression965);
			or_expr79=or_expr();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, or_expr79.getTree());

			}

			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (PseudoTree)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
			retval.tree = (PseudoTree)adaptor.errorNode(input, retval.start, input.LT(-1), re);
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
	// Pseudo.g:156:1: or_expr : and_expr ( ( '||' ^| '==>' ^) or_expr )? ;
	public final PseudoParser.or_expr_return or_expr() throws RecognitionException {
		PseudoParser.or_expr_return retval = new PseudoParser.or_expr_return();
		retval.start = input.LT(1);

		PseudoTree root_0 = null;

		Token string_literal81=null;
		Token string_literal82=null;
		ParserRuleReturnScope and_expr80 =null;
		ParserRuleReturnScope or_expr83 =null;

		PseudoTree string_literal81_tree=null;
		PseudoTree string_literal82_tree=null;

		try {
			// Pseudo.g:156:8: ( and_expr ( ( '||' ^| '==>' ^) or_expr )? )
			// Pseudo.g:157:3: and_expr ( ( '||' ^| '==>' ^) or_expr )?
			{
			root_0 = (PseudoTree)adaptor.nil();


			pushFollow(FOLLOW_and_expr_in_or_expr976);
			and_expr80=and_expr();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, and_expr80.getTree());

			// Pseudo.g:157:12: ( ( '||' ^| '==>' ^) or_expr )?
			int alt22=2;
			int LA22_0 = input.LA(1);
			if ( (LA22_0==IMPLIES||LA22_0==OR) ) {
				alt22=1;
			}
			switch (alt22) {
				case 1 :
					// Pseudo.g:157:14: ( '||' ^| '==>' ^) or_expr
					{
					// Pseudo.g:157:14: ( '||' ^| '==>' ^)
					int alt21=2;
					int LA21_0 = input.LA(1);
					if ( (LA21_0==OR) ) {
						alt21=1;
					}
					else if ( (LA21_0==IMPLIES) ) {
						alt21=2;
					}

					else {
						if (state.backtracking>0) {state.failed=true; return retval;}
						NoViableAltException nvae =
							new NoViableAltException("", 21, 0, input);
						throw nvae;
					}

					switch (alt21) {
						case 1 :
							// Pseudo.g:157:15: '||' ^
							{
							string_literal81=(Token)match(input,OR,FOLLOW_OR_in_or_expr981); if (state.failed) return retval;
							if ( state.backtracking==0 ) {
							string_literal81_tree = (PseudoTree)adaptor.create(string_literal81);
							root_0 = (PseudoTree)adaptor.becomeRoot(string_literal81_tree, root_0);
							}

							}
							break;
						case 2 :
							// Pseudo.g:157:23: '==>' ^
							{
							string_literal82=(Token)match(input,IMPLIES,FOLLOW_IMPLIES_in_or_expr986); if (state.failed) return retval;
							if ( state.backtracking==0 ) {
							string_literal82_tree = (PseudoTree)adaptor.create(string_literal82);
							root_0 = (PseudoTree)adaptor.becomeRoot(string_literal82_tree, root_0);
							}

							}
							break;

					}

					pushFollow(FOLLOW_or_expr_in_or_expr990);
					or_expr83=or_expr();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, or_expr83.getTree());

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
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
			retval.tree = (PseudoTree)adaptor.errorNode(input, retval.start, input.LT(-1), re);
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
	// Pseudo.g:160:1: and_expr : rel_expr ( '&&' ^ and_expr )? ;
	public final PseudoParser.and_expr_return and_expr() throws RecognitionException {
		PseudoParser.and_expr_return retval = new PseudoParser.and_expr_return();
		retval.start = input.LT(1);

		PseudoTree root_0 = null;

		Token string_literal85=null;
		ParserRuleReturnScope rel_expr84 =null;
		ParserRuleReturnScope and_expr86 =null;

		PseudoTree string_literal85_tree=null;

		try {
			// Pseudo.g:160:9: ( rel_expr ( '&&' ^ and_expr )? )
			// Pseudo.g:161:3: rel_expr ( '&&' ^ and_expr )?
			{
			root_0 = (PseudoTree)adaptor.nil();


			pushFollow(FOLLOW_rel_expr_in_and_expr1007);
			rel_expr84=rel_expr();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, rel_expr84.getTree());

			// Pseudo.g:161:12: ( '&&' ^ and_expr )?
			int alt23=2;
			int LA23_0 = input.LA(1);
			if ( (LA23_0==AND) ) {
				alt23=1;
			}
			switch (alt23) {
				case 1 :
					// Pseudo.g:161:14: '&&' ^ and_expr
					{
					string_literal85=(Token)match(input,AND,FOLLOW_AND_in_and_expr1011); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					string_literal85_tree = (PseudoTree)adaptor.create(string_literal85);
					root_0 = (PseudoTree)adaptor.becomeRoot(string_literal85_tree, root_0);
					}

					pushFollow(FOLLOW_and_expr_in_and_expr1014);
					and_expr86=and_expr();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, and_expr86.getTree());

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
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
			retval.tree = (PseudoTree)adaptor.errorNode(input, retval.start, input.LT(-1), re);
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
	// Pseudo.g:164:1: rel_expr : add_expr ( ( '<' ^| '>' ^| '=' ^| '<=' ^| '>=' ^) add_expr )? ;
	public final PseudoParser.rel_expr_return rel_expr() throws RecognitionException {
		PseudoParser.rel_expr_return retval = new PseudoParser.rel_expr_return();
		retval.start = input.LT(1);

		PseudoTree root_0 = null;

		Token char_literal88=null;
		Token char_literal89=null;
		Token char_literal90=null;
		Token string_literal91=null;
		Token string_literal92=null;
		ParserRuleReturnScope add_expr87 =null;
		ParserRuleReturnScope add_expr93 =null;

		PseudoTree char_literal88_tree=null;
		PseudoTree char_literal89_tree=null;
		PseudoTree char_literal90_tree=null;
		PseudoTree string_literal91_tree=null;
		PseudoTree string_literal92_tree=null;

		try {
			// Pseudo.g:164:9: ( add_expr ( ( '<' ^| '>' ^| '=' ^| '<=' ^| '>=' ^) add_expr )? )
			// Pseudo.g:165:3: add_expr ( ( '<' ^| '>' ^| '=' ^| '<=' ^| '>=' ^) add_expr )?
			{
			root_0 = (PseudoTree)adaptor.nil();


			pushFollow(FOLLOW_add_expr_in_rel_expr1029);
			add_expr87=add_expr();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, add_expr87.getTree());

			// Pseudo.g:165:12: ( ( '<' ^| '>' ^| '=' ^| '<=' ^| '>=' ^) add_expr )?
			int alt25=2;
			int LA25_0 = input.LA(1);
			if ( (LA25_0==EQ||(LA25_0 >= GE && LA25_0 <= GT)||LA25_0==LE||LA25_0==LT) ) {
				alt25=1;
			}
			switch (alt25) {
				case 1 :
					// Pseudo.g:165:14: ( '<' ^| '>' ^| '=' ^| '<=' ^| '>=' ^) add_expr
					{
					// Pseudo.g:165:14: ( '<' ^| '>' ^| '=' ^| '<=' ^| '>=' ^)
					int alt24=5;
					switch ( input.LA(1) ) {
					case LT:
						{
						alt24=1;
						}
						break;
					case GT:
						{
						alt24=2;
						}
						break;
					case EQ:
						{
						alt24=3;
						}
						break;
					case LE:
						{
						alt24=4;
						}
						break;
					case GE:
						{
						alt24=5;
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
							// Pseudo.g:165:15: '<' ^
							{
							char_literal88=(Token)match(input,LT,FOLLOW_LT_in_rel_expr1034); if (state.failed) return retval;
							if ( state.backtracking==0 ) {
							char_literal88_tree = (PseudoTree)adaptor.create(char_literal88);
							root_0 = (PseudoTree)adaptor.becomeRoot(char_literal88_tree, root_0);
							}

							}
							break;
						case 2 :
							// Pseudo.g:165:22: '>' ^
							{
							char_literal89=(Token)match(input,GT,FOLLOW_GT_in_rel_expr1039); if (state.failed) return retval;
							if ( state.backtracking==0 ) {
							char_literal89_tree = (PseudoTree)adaptor.create(char_literal89);
							root_0 = (PseudoTree)adaptor.becomeRoot(char_literal89_tree, root_0);
							}

							}
							break;
						case 3 :
							// Pseudo.g:165:29: '=' ^
							{
							char_literal90=(Token)match(input,EQ,FOLLOW_EQ_in_rel_expr1044); if (state.failed) return retval;
							if ( state.backtracking==0 ) {
							char_literal90_tree = (PseudoTree)adaptor.create(char_literal90);
							root_0 = (PseudoTree)adaptor.becomeRoot(char_literal90_tree, root_0);
							}

							}
							break;
						case 4 :
							// Pseudo.g:165:36: '<=' ^
							{
							string_literal91=(Token)match(input,LE,FOLLOW_LE_in_rel_expr1049); if (state.failed) return retval;
							if ( state.backtracking==0 ) {
							string_literal91_tree = (PseudoTree)adaptor.create(string_literal91);
							root_0 = (PseudoTree)adaptor.becomeRoot(string_literal91_tree, root_0);
							}

							}
							break;
						case 5 :
							// Pseudo.g:165:44: '>=' ^
							{
							string_literal92=(Token)match(input,GE,FOLLOW_GE_in_rel_expr1054); if (state.failed) return retval;
							if ( state.backtracking==0 ) {
							string_literal92_tree = (PseudoTree)adaptor.create(string_literal92);
							root_0 = (PseudoTree)adaptor.becomeRoot(string_literal92_tree, root_0);
							}

							}
							break;

					}

					pushFollow(FOLLOW_add_expr_in_rel_expr1058);
					add_expr93=add_expr();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, add_expr93.getTree());

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
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
			retval.tree = (PseudoTree)adaptor.errorNode(input, retval.start, input.LT(-1), re);
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
	// Pseudo.g:168:1: add_expr : mul_expr ( ( '+' | '-' | '++' ) ^ add_expr )? ;
	public final PseudoParser.add_expr_return add_expr() throws RecognitionException {
		PseudoParser.add_expr_return retval = new PseudoParser.add_expr_return();
		retval.start = input.LT(1);

		PseudoTree root_0 = null;

		Token set95=null;
		ParserRuleReturnScope mul_expr94 =null;
		ParserRuleReturnScope add_expr96 =null;

		PseudoTree set95_tree=null;

		try {
			// Pseudo.g:168:9: ( mul_expr ( ( '+' | '-' | '++' ) ^ add_expr )? )
			// Pseudo.g:169:3: mul_expr ( ( '+' | '-' | '++' ) ^ add_expr )?
			{
			root_0 = (PseudoTree)adaptor.nil();


			pushFollow(FOLLOW_mul_expr_in_add_expr1073);
			mul_expr94=mul_expr();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, mul_expr94.getTree());

			// Pseudo.g:169:12: ( ( '+' | '-' | '++' ) ^ add_expr )?
			int alt26=2;
			int LA26_0 = input.LA(1);
			if ( (LA26_0==MINUS||LA26_0==PLUS||LA26_0==UNION) ) {
				alt26=1;
			}
			switch (alt26) {
				case 1 :
					// Pseudo.g:169:14: ( '+' | '-' | '++' ) ^ add_expr
					{
					set95=input.LT(1);
					set95=input.LT(1);
					if ( input.LA(1)==MINUS||input.LA(1)==PLUS||input.LA(1)==UNION ) {
						input.consume();
						if ( state.backtracking==0 ) root_0 = (PseudoTree)adaptor.becomeRoot((PseudoTree)adaptor.create(set95), root_0);
						state.errorRecovery=false;
						state.failed=false;
					}
					else {
						if (state.backtracking>0) {state.failed=true; return retval;}
						MismatchedSetException mse = new MismatchedSetException(null,input);
						throw mse;
					}
					pushFollow(FOLLOW_add_expr_in_add_expr1090);
					add_expr96=add_expr();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, add_expr96.getTree());

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
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
			retval.tree = (PseudoTree)adaptor.errorNode(input, retval.start, input.LT(-1), re);
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
	// Pseudo.g:172:1: mul_expr : prefix_expr ( ( '*' | '**' ) ^ mul_expr )? ;
	public final PseudoParser.mul_expr_return mul_expr() throws RecognitionException {
		PseudoParser.mul_expr_return retval = new PseudoParser.mul_expr_return();
		retval.start = input.LT(1);

		PseudoTree root_0 = null;

		Token set98=null;
		ParserRuleReturnScope prefix_expr97 =null;
		ParserRuleReturnScope mul_expr99 =null;

		PseudoTree set98_tree=null;

		try {
			// Pseudo.g:172:9: ( prefix_expr ( ( '*' | '**' ) ^ mul_expr )? )
			// Pseudo.g:173:3: prefix_expr ( ( '*' | '**' ) ^ mul_expr )?
			{
			root_0 = (PseudoTree)adaptor.nil();


			pushFollow(FOLLOW_prefix_expr_in_mul_expr1105);
			prefix_expr97=prefix_expr();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, prefix_expr97.getTree());

			// Pseudo.g:173:15: ( ( '*' | '**' ) ^ mul_expr )?
			int alt27=2;
			int LA27_0 = input.LA(1);
			if ( (LA27_0==INTERSECT||LA27_0==TIMES) ) {
				alt27=1;
			}
			switch (alt27) {
				case 1 :
					// Pseudo.g:173:17: ( '*' | '**' ) ^ mul_expr
					{
					set98=input.LT(1);
					set98=input.LT(1);
					if ( input.LA(1)==INTERSECT||input.LA(1)==TIMES ) {
						input.consume();
						if ( state.backtracking==0 ) root_0 = (PseudoTree)adaptor.becomeRoot((PseudoTree)adaptor.create(set98), root_0);
						state.errorRecovery=false;
						state.failed=false;
					}
					else {
						if (state.backtracking>0) {state.failed=true; return retval;}
						MismatchedSetException mse = new MismatchedSetException(null,input);
						throw mse;
					}
					pushFollow(FOLLOW_mul_expr_in_mul_expr1118);
					mul_expr99=mul_expr();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, mul_expr99.getTree());

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
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
			retval.tree = (PseudoTree)adaptor.errorNode(input, retval.start, input.LT(-1), re);
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
	// Pseudo.g:176:1: prefix_expr : ( '-' ^ prefix_expr | 'not' ^ prefix_expr | postfix_expr );
	public final PseudoParser.prefix_expr_return prefix_expr() throws RecognitionException {
		PseudoParser.prefix_expr_return retval = new PseudoParser.prefix_expr_return();
		retval.start = input.LT(1);

		PseudoTree root_0 = null;

		Token char_literal100=null;
		Token string_literal102=null;
		ParserRuleReturnScope prefix_expr101 =null;
		ParserRuleReturnScope prefix_expr103 =null;
		ParserRuleReturnScope postfix_expr104 =null;

		PseudoTree char_literal100_tree=null;
		PseudoTree string_literal102_tree=null;

		try {
			// Pseudo.g:176:12: ( '-' ^ prefix_expr | 'not' ^ prefix_expr | postfix_expr )
			int alt28=3;
			switch ( input.LA(1) ) {
			case MINUS:
				{
				alt28=1;
				}
				break;
			case NOT:
				{
				alt28=2;
				}
				break;
			case ID:
			case LIT:
			case 45:
			case 50:
			case 55:
				{
				alt28=3;
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
					// Pseudo.g:177:5: '-' ^ prefix_expr
					{
					root_0 = (PseudoTree)adaptor.nil();


					char_literal100=(Token)match(input,MINUS,FOLLOW_MINUS_in_prefix_expr1135); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					char_literal100_tree = (PseudoTree)adaptor.create(char_literal100);
					root_0 = (PseudoTree)adaptor.becomeRoot(char_literal100_tree, root_0);
					}

					pushFollow(FOLLOW_prefix_expr_in_prefix_expr1138);
					prefix_expr101=prefix_expr();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, prefix_expr101.getTree());

					}
					break;
				case 2 :
					// Pseudo.g:178:5: 'not' ^ prefix_expr
					{
					root_0 = (PseudoTree)adaptor.nil();


					string_literal102=(Token)match(input,NOT,FOLLOW_NOT_in_prefix_expr1144); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					string_literal102_tree = (PseudoTree)adaptor.create(string_literal102);
					root_0 = (PseudoTree)adaptor.becomeRoot(string_literal102_tree, root_0);
					}

					pushFollow(FOLLOW_prefix_expr_in_prefix_expr1147);
					prefix_expr103=prefix_expr();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, prefix_expr103.getTree());

					}
					break;
				case 3 :
					// Pseudo.g:179:5: postfix_expr
					{
					root_0 = (PseudoTree)adaptor.nil();


					pushFollow(FOLLOW_postfix_expr_in_prefix_expr1153);
					postfix_expr104=postfix_expr();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, postfix_expr104.getTree());

					}
					break;

			}
			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (PseudoTree)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
			retval.tree = (PseudoTree)adaptor.errorNode(input, retval.start, input.LT(-1), re);
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
	// Pseudo.g:182:1: postfix_expr : atom_expr ( '[' expression ']' -> ^( ARRAY_ACCESS atom_expr expression ) | -> atom_expr ) ;
	public final PseudoParser.postfix_expr_return postfix_expr() throws RecognitionException {
		PseudoParser.postfix_expr_return retval = new PseudoParser.postfix_expr_return();
		retval.start = input.LT(1);

		PseudoTree root_0 = null;

		Token char_literal106=null;
		Token char_literal108=null;
		ParserRuleReturnScope atom_expr105 =null;
		ParserRuleReturnScope expression107 =null;

		PseudoTree char_literal106_tree=null;
		PseudoTree char_literal108_tree=null;
		RewriteRuleTokenStream stream_51=new RewriteRuleTokenStream(adaptor,"token 51");
		RewriteRuleTokenStream stream_50=new RewriteRuleTokenStream(adaptor,"token 50");
		RewriteRuleSubtreeStream stream_expression=new RewriteRuleSubtreeStream(adaptor,"rule expression");
		RewriteRuleSubtreeStream stream_atom_expr=new RewriteRuleSubtreeStream(adaptor,"rule atom_expr");

		try {
			// Pseudo.g:182:13: ( atom_expr ( '[' expression ']' -> ^( ARRAY_ACCESS atom_expr expression ) | -> atom_expr ) )
			// Pseudo.g:183:3: atom_expr ( '[' expression ']' -> ^( ARRAY_ACCESS atom_expr expression ) | -> atom_expr )
			{
			pushFollow(FOLLOW_atom_expr_in_postfix_expr1165);
			atom_expr105=atom_expr();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) stream_atom_expr.add(atom_expr105.getTree());
			// Pseudo.g:184:3: ( '[' expression ']' -> ^( ARRAY_ACCESS atom_expr expression ) | -> atom_expr )
			int alt29=2;
			int LA29_0 = input.LA(1);
			if ( (LA29_0==50) ) {
				alt29=1;
			}
			else if ( (LA29_0==AND||(LA29_0 >= DECREASES && LA29_0 <= EQ)||(LA29_0 >= GE && LA29_0 <= GT)||LA29_0==IMPLIES||(LA29_0 >= INTERSECT && LA29_0 <= LE)||(LA29_0 >= LT && LA29_0 <= MINUS)||(LA29_0 >= OR && LA29_0 <= REQUIRES)||(LA29_0 >= THEN && LA29_0 <= VAR)||(LA29_0 >= 46 && LA29_0 <= 47)||LA29_0==49||(LA29_0 >= 51 && LA29_0 <= 54)||LA29_0==56) ) {
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
					// Pseudo.g:184:5: '[' expression ']'
					{
					char_literal106=(Token)match(input,50,FOLLOW_50_in_postfix_expr1171); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_50.add(char_literal106);

					pushFollow(FOLLOW_expression_in_postfix_expr1173);
					expression107=expression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_expression.add(expression107.getTree());
					char_literal108=(Token)match(input,51,FOLLOW_51_in_postfix_expr1175); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_51.add(char_literal108);

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
					// 184:24: -> ^( ARRAY_ACCESS atom_expr expression )
					{
						// Pseudo.g:184:27: ^( ARRAY_ACCESS atom_expr expression )
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
					// Pseudo.g:185:5: 
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
					// 185:5: -> atom_expr
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
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
			retval.tree = (PseudoTree)adaptor.errorNode(input, retval.start, input.LT(-1), re);
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
	// Pseudo.g:188:1: atom_expr : ( ID | LIT | quantifier | '(' ! expression ')' !| '{' ( expressions )? '}' -> ^( SETEX ( expressions )? ) | '[' ( expressions )? ']' -> ^( LISTEX ( expressions )? ) );
	public final PseudoParser.atom_expr_return atom_expr() throws RecognitionException {
		PseudoParser.atom_expr_return retval = new PseudoParser.atom_expr_return();
		retval.start = input.LT(1);

		PseudoTree root_0 = null;

		Token ID109=null;
		Token LIT110=null;
		Token char_literal112=null;
		Token char_literal114=null;
		Token char_literal115=null;
		Token char_literal117=null;
		Token char_literal118=null;
		Token char_literal120=null;
		ParserRuleReturnScope quantifier111 =null;
		ParserRuleReturnScope expression113 =null;
		ParserRuleReturnScope expressions116 =null;
		ParserRuleReturnScope expressions119 =null;

		PseudoTree ID109_tree=null;
		PseudoTree LIT110_tree=null;
		PseudoTree char_literal112_tree=null;
		PseudoTree char_literal114_tree=null;
		PseudoTree char_literal115_tree=null;
		PseudoTree char_literal117_tree=null;
		PseudoTree char_literal118_tree=null;
		PseudoTree char_literal120_tree=null;
		RewriteRuleTokenStream stream_56=new RewriteRuleTokenStream(adaptor,"token 56");
		RewriteRuleTokenStream stream_55=new RewriteRuleTokenStream(adaptor,"token 55");
		RewriteRuleTokenStream stream_51=new RewriteRuleTokenStream(adaptor,"token 51");
		RewriteRuleTokenStream stream_50=new RewriteRuleTokenStream(adaptor,"token 50");
		RewriteRuleSubtreeStream stream_expressions=new RewriteRuleSubtreeStream(adaptor,"rule expressions");

		try {
			// Pseudo.g:188:10: ( ID | LIT | quantifier | '(' ! expression ')' !| '{' ( expressions )? '}' -> ^( SETEX ( expressions )? ) | '[' ( expressions )? ']' -> ^( LISTEX ( expressions )? ) )
			int alt32=6;
			switch ( input.LA(1) ) {
			case ID:
				{
				alt32=1;
				}
				break;
			case LIT:
				{
				alt32=2;
				}
				break;
			case 45:
				{
				int LA32_3 = input.LA(2);
				if ( (LA32_3==ALL||LA32_3==EX) ) {
					alt32=3;
				}
				else if ( (LA32_3==ID||LA32_3==LIT||(LA32_3 >= MINUS && LA32_3 <= NOT)||LA32_3==45||LA32_3==50||LA32_3==55) ) {
					alt32=4;
				}

				else {
					if (state.backtracking>0) {state.failed=true; return retval;}
					int nvaeMark = input.mark();
					try {
						input.consume();
						NoViableAltException nvae =
							new NoViableAltException("", 32, 3, input);
						throw nvae;
					} finally {
						input.rewind(nvaeMark);
					}
				}

				}
				break;
			case 55:
				{
				alt32=5;
				}
				break;
			case 50:
				{
				alt32=6;
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
					// Pseudo.g:189:5: ID
					{
					root_0 = (PseudoTree)adaptor.nil();


					ID109=(Token)match(input,ID,FOLLOW_ID_in_atom_expr1210); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					ID109_tree = (PseudoTree)adaptor.create(ID109);
					adaptor.addChild(root_0, ID109_tree);
					}

					}
					break;
				case 2 :
					// Pseudo.g:190:5: LIT
					{
					root_0 = (PseudoTree)adaptor.nil();


					LIT110=(Token)match(input,LIT,FOLLOW_LIT_in_atom_expr1216); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					LIT110_tree = (PseudoTree)adaptor.create(LIT110);
					adaptor.addChild(root_0, LIT110_tree);
					}

					}
					break;
				case 3 :
					// Pseudo.g:191:5: quantifier
					{
					root_0 = (PseudoTree)adaptor.nil();


					pushFollow(FOLLOW_quantifier_in_atom_expr1222);
					quantifier111=quantifier();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, quantifier111.getTree());

					}
					break;
				case 4 :
					// Pseudo.g:192:5: '(' ! expression ')' !
					{
					root_0 = (PseudoTree)adaptor.nil();


					char_literal112=(Token)match(input,45,FOLLOW_45_in_atom_expr1228); if (state.failed) return retval;
					pushFollow(FOLLOW_expression_in_atom_expr1231);
					expression113=expression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, expression113.getTree());

					char_literal114=(Token)match(input,46,FOLLOW_46_in_atom_expr1233); if (state.failed) return retval;
					}
					break;
				case 5 :
					// Pseudo.g:193:5: '{' ( expressions )? '}'
					{
					char_literal115=(Token)match(input,55,FOLLOW_55_in_atom_expr1240); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_55.add(char_literal115);

					// Pseudo.g:193:9: ( expressions )?
					int alt30=2;
					int LA30_0 = input.LA(1);
					if ( (LA30_0==ID||LA30_0==LIT||(LA30_0 >= MINUS && LA30_0 <= NOT)||LA30_0==45||LA30_0==50||LA30_0==55) ) {
						alt30=1;
					}
					switch (alt30) {
						case 1 :
							// Pseudo.g:193:9: expressions
							{
							pushFollow(FOLLOW_expressions_in_atom_expr1242);
							expressions116=expressions();
							state._fsp--;
							if (state.failed) return retval;
							if ( state.backtracking==0 ) stream_expressions.add(expressions116.getTree());
							}
							break;

					}

					char_literal117=(Token)match(input,56,FOLLOW_56_in_atom_expr1245); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_56.add(char_literal117);

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
					// 193:26: -> ^( SETEX ( expressions )? )
					{
						// Pseudo.g:193:29: ^( SETEX ( expressions )? )
						{
						PseudoTree root_1 = (PseudoTree)adaptor.nil();
						root_1 = (PseudoTree)adaptor.becomeRoot((PseudoTree)adaptor.create(SETEX, "SETEX"), root_1);
						// Pseudo.g:193:37: ( expressions )?
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
					// Pseudo.g:194:5: '[' ( expressions )? ']'
					{
					char_literal118=(Token)match(input,50,FOLLOW_50_in_atom_expr1260); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_50.add(char_literal118);

					// Pseudo.g:194:9: ( expressions )?
					int alt31=2;
					int LA31_0 = input.LA(1);
					if ( (LA31_0==ID||LA31_0==LIT||(LA31_0 >= MINUS && LA31_0 <= NOT)||LA31_0==45||LA31_0==50||LA31_0==55) ) {
						alt31=1;
					}
					switch (alt31) {
						case 1 :
							// Pseudo.g:194:9: expressions
							{
							pushFollow(FOLLOW_expressions_in_atom_expr1262);
							expressions119=expressions();
							state._fsp--;
							if (state.failed) return retval;
							if ( state.backtracking==0 ) stream_expressions.add(expressions119.getTree());
							}
							break;

					}

					char_literal120=(Token)match(input,51,FOLLOW_51_in_atom_expr1265); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_51.add(char_literal120);

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
					// 194:26: -> ^( LISTEX ( expressions )? )
					{
						// Pseudo.g:194:29: ^( LISTEX ( expressions )? )
						{
						PseudoTree root_1 = (PseudoTree)adaptor.nil();
						root_1 = (PseudoTree)adaptor.becomeRoot((PseudoTree)adaptor.create(LISTEX, "LISTEX"), root_1);
						// Pseudo.g:194:38: ( expressions )?
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
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
			retval.tree = (PseudoTree)adaptor.errorNode(input, retval.start, input.LT(-1), re);
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
	// Pseudo.g:197:1: quantifier : '(' ! ( ALL ^| EX ^) ID ':' ! type ';' ! expression ')' !;
	public final PseudoParser.quantifier_return quantifier() throws RecognitionException {
		PseudoParser.quantifier_return retval = new PseudoParser.quantifier_return();
		retval.start = input.LT(1);

		PseudoTree root_0 = null;

		Token char_literal121=null;
		Token ALL122=null;
		Token EX123=null;
		Token ID124=null;
		Token char_literal125=null;
		Token char_literal127=null;
		Token char_literal129=null;
		ParserRuleReturnScope type126 =null;
		ParserRuleReturnScope expression128 =null;

		PseudoTree char_literal121_tree=null;
		PseudoTree ALL122_tree=null;
		PseudoTree EX123_tree=null;
		PseudoTree ID124_tree=null;
		PseudoTree char_literal125_tree=null;
		PseudoTree char_literal127_tree=null;
		PseudoTree char_literal129_tree=null;

		try {
			// Pseudo.g:197:11: ( '(' ! ( ALL ^| EX ^) ID ':' ! type ';' ! expression ')' !)
			// Pseudo.g:198:3: '(' ! ( ALL ^| EX ^) ID ':' ! type ';' ! expression ')' !
			{
			root_0 = (PseudoTree)adaptor.nil();


			char_literal121=(Token)match(input,45,FOLLOW_45_in_quantifier1286); if (state.failed) return retval;
			// Pseudo.g:198:8: ( ALL ^| EX ^)
			int alt33=2;
			int LA33_0 = input.LA(1);
			if ( (LA33_0==ALL) ) {
				alt33=1;
			}
			else if ( (LA33_0==EX) ) {
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
					// Pseudo.g:198:9: ALL ^
					{
					ALL122=(Token)match(input,ALL,FOLLOW_ALL_in_quantifier1290); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					ALL122_tree = (PseudoTree)adaptor.create(ALL122);
					root_0 = (PseudoTree)adaptor.becomeRoot(ALL122_tree, root_0);
					}

					}
					break;
				case 2 :
					// Pseudo.g:198:16: EX ^
					{
					EX123=(Token)match(input,EX,FOLLOW_EX_in_quantifier1295); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					EX123_tree = (PseudoTree)adaptor.create(EX123);
					root_0 = (PseudoTree)adaptor.becomeRoot(EX123_tree, root_0);
					}

					}
					break;

			}

			ID124=(Token)match(input,ID,FOLLOW_ID_in_quantifier1299); if (state.failed) return retval;
			if ( state.backtracking==0 ) {
			ID124_tree = (PseudoTree)adaptor.create(ID124);
			adaptor.addChild(root_0, ID124_tree);
			}

			char_literal125=(Token)match(input,48,FOLLOW_48_in_quantifier1301); if (state.failed) return retval;
			pushFollow(FOLLOW_type_in_quantifier1304);
			type126=type();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, type126.getTree());

			char_literal127=(Token)match(input,49,FOLLOW_49_in_quantifier1306); if (state.failed) return retval;
			pushFollow(FOLLOW_expression_in_quantifier1309);
			expression128=expression();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, expression128.getTree());

			char_literal129=(Token)match(input,46,FOLLOW_46_in_quantifier1311); if (state.failed) return retval;
			}

			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (PseudoTree)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
			retval.tree = (PseudoTree)adaptor.errorNode(input, retval.start, input.LT(-1), re);
		}
		finally {
			// do for sure before leaving
		}
		return retval;
	}
	// $ANTLR end "quantifier"

	// $ANTLR start synpred1_Pseudo
	public final void synpred1_Pseudo_fragment() throws RecognitionException {
		// Pseudo.g:133:5: ( ID ':=' 'call' )
		// Pseudo.g:133:6: ID ':=' 'call'
		{
		match(input,ID,FOLLOW_ID_in_synpred1_Pseudo728); if (state.failed) return;

		match(input,ASSIGN,FOLLOW_ASSIGN_in_synpred1_Pseudo730); if (state.failed) return;

		match(input,CALL,FOLLOW_CALL_in_synpred1_Pseudo732); if (state.failed) return;

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



	public static final BitSet FOLLOW_function_in_program325 = new BitSet(new long[]{0x0000000000020002L});
	public static final BitSet FOLLOW_FUNCTION_in_function339 = new BitSet(new long[]{0x0000000000100000L});
	public static final BitSet FOLLOW_ID_in_function341 = new BitSet(new long[]{0x0000200000000000L});
	public static final BitSet FOLLOW_45_in_function343 = new BitSet(new long[]{0x0000400000100000L});
	public static final BitSet FOLLOW_vars_in_function345 = new BitSet(new long[]{0x0000400000000000L});
	public static final BitSet FOLLOW_46_in_function348 = new BitSet(new long[]{0x0010041400005000L});
	public static final BitSet FOLLOW_return__in_function354 = new BitSet(new long[]{0x0010040400005000L});
	public static final BitSet FOLLOW_requires_in_function363 = new BitSet(new long[]{0x0010040400005000L});
	public static final BitSet FOLLOW_ensures_in_function372 = new BitSet(new long[]{0x0010040000005000L});
	public static final BitSet FOLLOW_decreases_in_function381 = new BitSet(new long[]{0x0010040000000000L});
	public static final BitSet FOLLOW_decl_in_function390 = new BitSet(new long[]{0x0010000000000000L});
	public static final BitSet FOLLOW_block_in_function397 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_var_in_vars456 = new BitSet(new long[]{0x0000800000000002L});
	public static final BitSet FOLLOW_47_in_vars462 = new BitSet(new long[]{0x0000000000100000L});
	public static final BitSet FOLLOW_var_in_vars465 = new BitSet(new long[]{0x0000800000000002L});
	public static final BitSet FOLLOW_ID_in_var480 = new BitSet(new long[]{0x0001000000000000L});
	public static final BitSet FOLLOW_48_in_var482 = new BitSet(new long[]{0x0000002000800080L});
	public static final BitSet FOLLOW_type_in_var484 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_RETURNS_in_return_526 = new BitSet(new long[]{0x0000000000100000L});
	public static final BitSet FOLLOW_vars_in_return_529 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_REQUIRES_in_requires541 = new BitSet(new long[]{0x00842000D0100000L});
	public static final BitSet FOLLOW_ID_in_requires545 = new BitSet(new long[]{0x0001000000000000L});
	public static final BitSet FOLLOW_48_in_requires547 = new BitSet(new long[]{0x00842000D0100000L});
	public static final BitSet FOLLOW_expression_in_requires552 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_ENSURES_in_ensures564 = new BitSet(new long[]{0x00842000D0100000L});
	public static final BitSet FOLLOW_ID_in_ensures568 = new BitSet(new long[]{0x0001000000000000L});
	public static final BitSet FOLLOW_48_in_ensures570 = new BitSet(new long[]{0x00842000D0100000L});
	public static final BitSet FOLLOW_expression_in_ensures575 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_DECREASES_in_decreases587 = new BitSet(new long[]{0x00842000D0100000L});
	public static final BitSet FOLLOW_expression_in_decreases590 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_INVARIANT_in_invariant602 = new BitSet(new long[]{0x00842000D0100000L});
	public static final BitSet FOLLOW_ID_in_invariant606 = new BitSet(new long[]{0x0001000000000000L});
	public static final BitSet FOLLOW_48_in_invariant608 = new BitSet(new long[]{0x00842000D0100000L});
	public static final BitSet FOLLOW_expression_in_invariant613 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_VAR_in_decl625 = new BitSet(new long[]{0x0000000000100000L});
	public static final BitSet FOLLOW_vars_in_decl628 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_52_in_block640 = new BitSet(new long[]{0x0000080000300000L});
	public static final BitSet FOLLOW_statements_in_block642 = new BitSet(new long[]{0x0040000000000000L});
	public static final BitSet FOLLOW_54_in_block644 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_block_in_relaxedBlock666 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_statement_in_relaxedBlock672 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_statement_in_statements692 = new BitSet(new long[]{0x0002000000000002L});
	public static final BitSet FOLLOW_49_in_statements696 = new BitSet(new long[]{0x0000080000300000L});
	public static final BitSet FOLLOW_statement_in_statements699 = new BitSet(new long[]{0x0002000000000002L});
	public static final BitSet FOLLOW_ID_in_statement716 = new BitSet(new long[]{0x0000000000000200L});
	public static final BitSet FOLLOW_ASSIGN_in_statement718 = new BitSet(new long[]{0x00842000D0100000L});
	public static final BitSet FOLLOW_expression_in_statement721 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_ID_in_statement739 = new BitSet(new long[]{0x0000000000000200L});
	public static final BitSet FOLLOW_ASSIGN_in_statement741 = new BitSet(new long[]{0x0000000000000800L});
	public static final BitSet FOLLOW_CALL_in_statement743 = new BitSet(new long[]{0x0000000000100000L});
	public static final BitSet FOLLOW_ID_in_statement747 = new BitSet(new long[]{0x0000200000000000L});
	public static final BitSet FOLLOW_45_in_statement749 = new BitSet(new long[]{0x00846000D0100000L});
	public static final BitSet FOLLOW_expressions_in_statement751 = new BitSet(new long[]{0x0000400000000000L});
	public static final BitSet FOLLOW_46_in_statement754 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_ids_in_statement791 = new BitSet(new long[]{0x0000000000000200L});
	public static final BitSet FOLLOW_ASSIGN_in_statement793 = new BitSet(new long[]{0x0000000000000800L});
	public static final BitSet FOLLOW_CALL_in_statement795 = new BitSet(new long[]{0x0000000000100000L});
	public static final BitSet FOLLOW_ID_in_statement797 = new BitSet(new long[]{0x0000200000000000L});
	public static final BitSet FOLLOW_45_in_statement799 = new BitSet(new long[]{0x00846000D0100000L});
	public static final BitSet FOLLOW_expressions_in_statement801 = new BitSet(new long[]{0x0000400000000000L});
	public static final BitSet FOLLOW_46_in_statement804 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_WHILE_in_statement839 = new BitSet(new long[]{0x00842000D0100000L});
	public static final BitSet FOLLOW_expression_in_statement842 = new BitSet(new long[]{0x0000000002000000L});
	public static final BitSet FOLLOW_invariant_in_statement850 = new BitSet(new long[]{0x0000000002001000L});
	public static final BitSet FOLLOW_decreases_in_statement859 = new BitSet(new long[]{0x0020000000000000L});
	public static final BitSet FOLLOW_53_in_statement867 = new BitSet(new long[]{0x0010080000300000L});
	public static final BitSet FOLLOW_relaxedBlock_in_statement870 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_IF_in_statement876 = new BitSet(new long[]{0x00842000D0100000L});
	public static final BitSet FOLLOW_expression_in_statement879 = new BitSet(new long[]{0x0000008000000000L});
	public static final BitSet FOLLOW_THEN_in_statement881 = new BitSet(new long[]{0x0010080000300000L});
	public static final BitSet FOLLOW_relaxedBlock_in_statement884 = new BitSet(new long[]{0x0000000000002002L});
	public static final BitSet FOLLOW_ELSE_in_statement905 = new BitSet(new long[]{0x0010080000300000L});
	public static final BitSet FOLLOW_relaxedBlock_in_statement908 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_ID_in_ids923 = new BitSet(new long[]{0x0000800000000000L});
	public static final BitSet FOLLOW_47_in_ids926 = new BitSet(new long[]{0x0000000000100000L});
	public static final BitSet FOLLOW_ID_in_ids929 = new BitSet(new long[]{0x0000800000000002L});
	public static final BitSet FOLLOW_expression_in_expressions943 = new BitSet(new long[]{0x0000800000000002L});
	public static final BitSet FOLLOW_47_in_expressions947 = new BitSet(new long[]{0x00842000D0100000L});
	public static final BitSet FOLLOW_expression_in_expressions950 = new BitSet(new long[]{0x0000800000000002L});
	public static final BitSet FOLLOW_or_expr_in_expression965 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_and_expr_in_or_expr976 = new BitSet(new long[]{0x0000000100400002L});
	public static final BitSet FOLLOW_OR_in_or_expr981 = new BitSet(new long[]{0x00842000D0100000L});
	public static final BitSet FOLLOW_IMPLIES_in_or_expr986 = new BitSet(new long[]{0x00842000D0100000L});
	public static final BitSet FOLLOW_or_expr_in_or_expr990 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_rel_expr_in_and_expr1007 = new BitSet(new long[]{0x0000000000000022L});
	public static final BitSet FOLLOW_AND_in_and_expr1011 = new BitSet(new long[]{0x00842000D0100000L});
	public static final BitSet FOLLOW_and_expr_in_and_expr1014 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_add_expr_in_rel_expr1029 = new BitSet(new long[]{0x00000000240C8002L});
	public static final BitSet FOLLOW_LT_in_rel_expr1034 = new BitSet(new long[]{0x00842000D0100000L});
	public static final BitSet FOLLOW_GT_in_rel_expr1039 = new BitSet(new long[]{0x00842000D0100000L});
	public static final BitSet FOLLOW_EQ_in_rel_expr1044 = new BitSet(new long[]{0x00842000D0100000L});
	public static final BitSet FOLLOW_LE_in_rel_expr1049 = new BitSet(new long[]{0x00842000D0100000L});
	public static final BitSet FOLLOW_GE_in_rel_expr1054 = new BitSet(new long[]{0x00842000D0100000L});
	public static final BitSet FOLLOW_add_expr_in_rel_expr1058 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_mul_expr_in_add_expr1073 = new BitSet(new long[]{0x0000020240000002L});
	public static final BitSet FOLLOW_set_in_add_expr1077 = new BitSet(new long[]{0x00842000D0100000L});
	public static final BitSet FOLLOW_add_expr_in_add_expr1090 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_prefix_expr_in_mul_expr1105 = new BitSet(new long[]{0x0000010001000002L});
	public static final BitSet FOLLOW_set_in_mul_expr1109 = new BitSet(new long[]{0x00842000D0100000L});
	public static final BitSet FOLLOW_mul_expr_in_mul_expr1118 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_MINUS_in_prefix_expr1135 = new BitSet(new long[]{0x00842000D0100000L});
	public static final BitSet FOLLOW_prefix_expr_in_prefix_expr1138 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_NOT_in_prefix_expr1144 = new BitSet(new long[]{0x00842000D0100000L});
	public static final BitSet FOLLOW_prefix_expr_in_prefix_expr1147 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_postfix_expr_in_prefix_expr1153 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_atom_expr_in_postfix_expr1165 = new BitSet(new long[]{0x0004000000000002L});
	public static final BitSet FOLLOW_50_in_postfix_expr1171 = new BitSet(new long[]{0x00842000D0100000L});
	public static final BitSet FOLLOW_expression_in_postfix_expr1173 = new BitSet(new long[]{0x0008000000000000L});
	public static final BitSet FOLLOW_51_in_postfix_expr1175 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_ID_in_atom_expr1210 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_LIT_in_atom_expr1216 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_quantifier_in_atom_expr1222 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_45_in_atom_expr1228 = new BitSet(new long[]{0x00842000D0100000L});
	public static final BitSet FOLLOW_expression_in_atom_expr1231 = new BitSet(new long[]{0x0000400000000000L});
	public static final BitSet FOLLOW_46_in_atom_expr1233 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_55_in_atom_expr1240 = new BitSet(new long[]{0x01842000D0100000L});
	public static final BitSet FOLLOW_expressions_in_atom_expr1242 = new BitSet(new long[]{0x0100000000000000L});
	public static final BitSet FOLLOW_56_in_atom_expr1245 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_50_in_atom_expr1260 = new BitSet(new long[]{0x008C2000D0100000L});
	public static final BitSet FOLLOW_expressions_in_atom_expr1262 = new BitSet(new long[]{0x0008000000000000L});
	public static final BitSet FOLLOW_51_in_atom_expr1265 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_45_in_quantifier1286 = new BitSet(new long[]{0x0000000000010010L});
	public static final BitSet FOLLOW_ALL_in_quantifier1290 = new BitSet(new long[]{0x0000000000100000L});
	public static final BitSet FOLLOW_EX_in_quantifier1295 = new BitSet(new long[]{0x0000000000100000L});
	public static final BitSet FOLLOW_ID_in_quantifier1299 = new BitSet(new long[]{0x0001000000000000L});
	public static final BitSet FOLLOW_48_in_quantifier1301 = new BitSet(new long[]{0x0000002000800080L});
	public static final BitSet FOLLOW_type_in_quantifier1304 = new BitSet(new long[]{0x0002000000000000L});
	public static final BitSet FOLLOW_49_in_quantifier1306 = new BitSet(new long[]{0x00842000D0100000L});
	public static final BitSet FOLLOW_expression_in_quantifier1309 = new BitSet(new long[]{0x0000400000000000L});
	public static final BitSet FOLLOW_46_in_quantifier1311 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_ID_in_synpred1_Pseudo728 = new BitSet(new long[]{0x0000000000000200L});
	public static final BitSet FOLLOW_ASSIGN_in_synpred1_Pseudo730 = new BitSet(new long[]{0x0000000000000800L});
	public static final BitSet FOLLOW_CALL_in_synpred1_Pseudo732 = new BitSet(new long[]{0x0000000000000002L});
}
