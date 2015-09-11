// $ANTLR 3.2 debian-7ubuntu3 src/edu/kit/iti/algover/parser/Pseudo.g 2015-09-09 22:09:02

  package edu.kit.iti.algover.parser;


import org.antlr.runtime.*;
import java.util.Stack;
import java.util.List;
import java.util.ArrayList;
import java.util.Map;
import java.util.HashMap;

import org.antlr.runtime.tree.*;

public class PseudoParser extends Parser {
    public static final String[] tokenNames = new String[] {
        "<invalid>", "<EOR>", "<DOWN>", "<UP>", "RESULTS", "ARGS", "BLOCK", "LISTEX", "SETEX", "ARRAY_ACCESS", "INT", "SET", "RETURNS", "ENSURES", "REQUIRES", "DECREASES", "METHOD", "ELSE", "IF", "THEN", "WHILE", "VAR", "CALL", "INVARIANT", "ASSERT", "ASSUME", "ALL", "EX", "DOUBLECOLON", "ASSIGN", "OR", "AND", "IMPLIES", "PLUS", "MINUS", "NOT", "TIMES", "UNION", "INTERSECT", "LT", "LE", "GT", "GE", "EQ", "BLOCK_BEGIN", "BLOCK_END", "ARRAY", "ID", "LIT", "WS", "'('", "')'", "';'", "','", "':'", "'assume'", "'['", "']'"
    };
    public static final int LT=39;
    public static final int WHILE=20;
    public static final int NOT=35;
    public static final int ID=47;
    public static final int AND=31;
    public static final int EOF=-1;
    public static final int IF=18;
    public static final int LISTEX=7;
    public static final int T__55=55;
    public static final int T__56=56;
    public static final int ENSURES=13;
    public static final int T__57=57;
    public static final int T__51=51;
    public static final int T__52=52;
    public static final int THEN=19;
    public static final int T__53=53;
    public static final int T__54=54;
    public static final int EX=27;
    public static final int ALL=26;
    public static final int BLOCK_END=45;
    public static final int ARGS=5;
    public static final int PLUS=33;
    public static final int VAR=21;
    public static final int EQ=43;
    public static final int BLOCK_BEGIN=44;
    public static final int T__50=50;
    public static final int ARRAY=46;
    public static final int SETEX=8;
    public static final int RETURNS=12;
    public static final int DOUBLECOLON=28;
    public static final int GE=42;
    public static final int IMPLIES=32;
    public static final int ELSE=17;
    public static final int LIT=48;
    public static final int INVARIANT=23;
    public static final int SET=11;
    public static final int INT=10;
    public static final int ARRAY_ACCESS=9;
    public static final int MINUS=34;
    public static final int RESULTS=4;
    public static final int ASSERT=24;
    public static final int UNION=37;
    public static final int INTERSECT=38;
    public static final int WS=49;
    public static final int REQUIRES=14;
    public static final int ASSUME=25;
    public static final int BLOCK=6;
    public static final int OR=30;
    public static final int ASSIGN=29;
    public static final int GT=41;
    public static final int DECREASES=15;
    public static final int CALL=22;
    public static final int TIMES=36;
    public static final int METHOD=16;
    public static final int LE=40;

    // delegates
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

    public String[] getTokenNames() { return PseudoParser.tokenNames; }
    public String getGrammarFileName() { return "src/edu/kit/iti/algover/parser/Pseudo.g"; }


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
        public Object getTree() { return tree; }
    };

    // $ANTLR start "program"
    // src/edu/kit/iti/algover/parser/Pseudo.g:102:1: program : ( method )+ ;
    public final PseudoParser.program_return program() throws RecognitionException {
        PseudoParser.program_return retval = new PseudoParser.program_return();
        retval.start = input.LT(1);

        PseudoTree root_0 = null;

        PseudoParser.method_return method1 = null;



        try {
            // src/edu/kit/iti/algover/parser/Pseudo.g:102:8: ( ( method )+ )
            // src/edu/kit/iti/algover/parser/Pseudo.g:103:3: ( method )+
            {
            root_0 = (PseudoTree)adaptor.nil();

            // src/edu/kit/iti/algover/parser/Pseudo.g:103:3: ( method )+
            int cnt1=0;
            loop1:
            do {
                int alt1=2;
                int LA1_0 = input.LA(1);

                if ( (LA1_0==METHOD) ) {
                    alt1=1;
                }


                switch (alt1) {
            	case 1 :
            	    // src/edu/kit/iti/algover/parser/Pseudo.g:103:3: method
            	    {
            	    pushFollow(FOLLOW_method_in_program409);
            	    method1=method();

            	    state._fsp--;
            	    if (state.failed) return retval;
            	    if ( state.backtracking==0 ) adaptor.addChild(root_0, method1.getTree());

            	    }
            	    break;

            	default :
            	    if ( cnt1 >= 1 ) break loop1;
            	    if (state.backtracking>0) {state.failed=true; return retval;}
                        EarlyExitException eee =
                            new EarlyExitException(1, input);
                        throw eee;
                }
                cnt1++;
            } while (true);


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
        }
        return retval;
    }
    // $ANTLR end "program"

    public static class method_return extends ParserRuleReturnScope {
        PseudoTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start "method"
    // src/edu/kit/iti/algover/parser/Pseudo.g:106:1: method : 'method' ID '(' ( vars )? ')' ( returns_ )? ( requires )* ( ensures )* ( decreases )? '{' ( decl )* ( statements )? '}' -> ^( 'method' ID ^( ARGS ( vars )? ) ( returns_ )? ( requires )* ( ensures )* ( decreases )? ( decl )* ^( BLOCK ( statements )? ) ) ;
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
        PseudoParser.vars_return vars5 = null;

        PseudoParser.returns__return returns_7 = null;

        PseudoParser.requires_return requires8 = null;

        PseudoParser.ensures_return ensures9 = null;

        PseudoParser.decreases_return decreases10 = null;

        PseudoParser.decl_return decl12 = null;

        PseudoParser.statements_return statements13 = null;


        PseudoTree string_literal2_tree=null;
        PseudoTree ID3_tree=null;
        PseudoTree char_literal4_tree=null;
        PseudoTree char_literal6_tree=null;
        PseudoTree char_literal11_tree=null;
        PseudoTree char_literal14_tree=null;
        RewriteRuleTokenStream stream_51=new RewriteRuleTokenStream(adaptor,"token 51");
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
            // src/edu/kit/iti/algover/parser/Pseudo.g:106:7: ( 'method' ID '(' ( vars )? ')' ( returns_ )? ( requires )* ( ensures )* ( decreases )? '{' ( decl )* ( statements )? '}' -> ^( 'method' ID ^( ARGS ( vars )? ) ( returns_ )? ( requires )* ( ensures )* ( decreases )? ( decl )* ^( BLOCK ( statements )? ) ) )
            // src/edu/kit/iti/algover/parser/Pseudo.g:107:3: 'method' ID '(' ( vars )? ')' ( returns_ )? ( requires )* ( ensures )* ( decreases )? '{' ( decl )* ( statements )? '}'
            {
            string_literal2=(Token)match(input,METHOD,FOLLOW_METHOD_in_method423); if (state.failed) return retval; 
            if ( state.backtracking==0 ) stream_METHOD.add(string_literal2);

            ID3=(Token)match(input,ID,FOLLOW_ID_in_method425); if (state.failed) return retval; 
            if ( state.backtracking==0 ) stream_ID.add(ID3);

            char_literal4=(Token)match(input,50,FOLLOW_50_in_method427); if (state.failed) return retval; 
            if ( state.backtracking==0 ) stream_50.add(char_literal4);

            // src/edu/kit/iti/algover/parser/Pseudo.g:107:19: ( vars )?
            int alt2=2;
            int LA2_0 = input.LA(1);

            if ( (LA2_0==ID) ) {
                alt2=1;
            }
            switch (alt2) {
                case 1 :
                    // src/edu/kit/iti/algover/parser/Pseudo.g:107:19: vars
                    {
                    pushFollow(FOLLOW_vars_in_method429);
                    vars5=vars();

                    state._fsp--;
                    if (state.failed) return retval;
                    if ( state.backtracking==0 ) stream_vars.add(vars5.getTree());

                    }
                    break;

            }

            char_literal6=(Token)match(input,51,FOLLOW_51_in_method432); if (state.failed) return retval; 
            if ( state.backtracking==0 ) stream_51.add(char_literal6);

            // src/edu/kit/iti/algover/parser/Pseudo.g:108:3: ( returns_ )?
            int alt3=2;
            int LA3_0 = input.LA(1);

            if ( (LA3_0==RETURNS) ) {
                alt3=1;
            }
            switch (alt3) {
                case 1 :
                    // src/edu/kit/iti/algover/parser/Pseudo.g:108:5: returns_
                    {
                    pushFollow(FOLLOW_returns__in_method438);
                    returns_7=returns_();

                    state._fsp--;
                    if (state.failed) return retval;
                    if ( state.backtracking==0 ) stream_returns_.add(returns_7.getTree());

                    }
                    break;

            }

            // src/edu/kit/iti/algover/parser/Pseudo.g:109:3: ( requires )*
            loop4:
            do {
                int alt4=2;
                int LA4_0 = input.LA(1);

                if ( (LA4_0==REQUIRES) ) {
                    alt4=1;
                }


                switch (alt4) {
            	case 1 :
            	    // src/edu/kit/iti/algover/parser/Pseudo.g:109:5: requires
            	    {
            	    pushFollow(FOLLOW_requires_in_method447);
            	    requires8=requires();

            	    state._fsp--;
            	    if (state.failed) return retval;
            	    if ( state.backtracking==0 ) stream_requires.add(requires8.getTree());

            	    }
            	    break;

            	default :
            	    break loop4;
                }
            } while (true);

            // src/edu/kit/iti/algover/parser/Pseudo.g:110:3: ( ensures )*
            loop5:
            do {
                int alt5=2;
                int LA5_0 = input.LA(1);

                if ( (LA5_0==ENSURES) ) {
                    alt5=1;
                }


                switch (alt5) {
            	case 1 :
            	    // src/edu/kit/iti/algover/parser/Pseudo.g:110:5: ensures
            	    {
            	    pushFollow(FOLLOW_ensures_in_method456);
            	    ensures9=ensures();

            	    state._fsp--;
            	    if (state.failed) return retval;
            	    if ( state.backtracking==0 ) stream_ensures.add(ensures9.getTree());

            	    }
            	    break;

            	default :
            	    break loop5;
                }
            } while (true);

            // src/edu/kit/iti/algover/parser/Pseudo.g:111:3: ( decreases )?
            int alt6=2;
            int LA6_0 = input.LA(1);

            if ( (LA6_0==DECREASES) ) {
                alt6=1;
            }
            switch (alt6) {
                case 1 :
                    // src/edu/kit/iti/algover/parser/Pseudo.g:111:5: decreases
                    {
                    pushFollow(FOLLOW_decreases_in_method465);
                    decreases10=decreases();

                    state._fsp--;
                    if (state.failed) return retval;
                    if ( state.backtracking==0 ) stream_decreases.add(decreases10.getTree());

                    }
                    break;

            }

            char_literal11=(Token)match(input,BLOCK_BEGIN,FOLLOW_BLOCK_BEGIN_in_method472); if (state.failed) return retval; 
            if ( state.backtracking==0 ) stream_BLOCK_BEGIN.add(char_literal11);

            // src/edu/kit/iti/algover/parser/Pseudo.g:112:7: ( decl )*
            loop7:
            do {
                int alt7=2;
                int LA7_0 = input.LA(1);

                if ( (LA7_0==VAR) ) {
                    alt7=1;
                }


                switch (alt7) {
            	case 1 :
            	    // src/edu/kit/iti/algover/parser/Pseudo.g:112:9: decl
            	    {
            	    pushFollow(FOLLOW_decl_in_method476);
            	    decl12=decl();

            	    state._fsp--;
            	    if (state.failed) return retval;
            	    if ( state.backtracking==0 ) stream_decl.add(decl12.getTree());

            	    }
            	    break;

            	default :
            	    break loop7;
                }
            } while (true);

            // src/edu/kit/iti/algover/parser/Pseudo.g:112:17: ( statements )?
            int alt8=2;
            int LA8_0 = input.LA(1);

            if ( (LA8_0==IF||LA8_0==WHILE||LA8_0==ASSERT||LA8_0==ID||LA8_0==55) ) {
                alt8=1;
            }
            switch (alt8) {
                case 1 :
                    // src/edu/kit/iti/algover/parser/Pseudo.g:112:17: statements
                    {
                    pushFollow(FOLLOW_statements_in_method481);
                    statements13=statements();

                    state._fsp--;
                    if (state.failed) return retval;
                    if ( state.backtracking==0 ) stream_statements.add(statements13.getTree());

                    }
                    break;

            }

            char_literal14=(Token)match(input,BLOCK_END,FOLLOW_BLOCK_END_in_method484); if (state.failed) return retval; 
            if ( state.backtracking==0 ) stream_BLOCK_END.add(char_literal14);



            // AST REWRITE
            // elements: decl, requires, decreases, ensures, returns_, ID, METHOD, vars, statements
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            // wildcard labels: 
            if ( state.backtracking==0 ) {
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.tree:null);

            root_0 = (PseudoTree)adaptor.nil();
            // 113:3: -> ^( 'method' ID ^( ARGS ( vars )? ) ( returns_ )? ( requires )* ( ensures )* ( decreases )? ( decl )* ^( BLOCK ( statements )? ) )
            {
                // src/edu/kit/iti/algover/parser/Pseudo.g:114:5: ^( 'method' ID ^( ARGS ( vars )? ) ( returns_ )? ( requires )* ( ensures )* ( decreases )? ( decl )* ^( BLOCK ( statements )? ) )
                {
                PseudoTree root_1 = (PseudoTree)adaptor.nil();
                root_1 = (PseudoTree)adaptor.becomeRoot(stream_METHOD.nextNode(), root_1);

                adaptor.addChild(root_1, stream_ID.nextNode());
                // src/edu/kit/iti/algover/parser/Pseudo.g:114:19: ^( ARGS ( vars )? )
                {
                PseudoTree root_2 = (PseudoTree)adaptor.nil();
                root_2 = (PseudoTree)adaptor.becomeRoot((PseudoTree)adaptor.create(ARGS, "ARGS"), root_2);

                // src/edu/kit/iti/algover/parser/Pseudo.g:114:26: ( vars )?
                if ( stream_vars.hasNext() ) {
                    adaptor.addChild(root_2, stream_vars.nextTree());

                }
                stream_vars.reset();

                adaptor.addChild(root_1, root_2);
                }
                // src/edu/kit/iti/algover/parser/Pseudo.g:114:33: ( returns_ )?
                if ( stream_returns_.hasNext() ) {
                    adaptor.addChild(root_1, stream_returns_.nextTree());

                }
                stream_returns_.reset();
                // src/edu/kit/iti/algover/parser/Pseudo.g:114:43: ( requires )*
                while ( stream_requires.hasNext() ) {
                    adaptor.addChild(root_1, stream_requires.nextTree());

                }
                stream_requires.reset();
                // src/edu/kit/iti/algover/parser/Pseudo.g:114:53: ( ensures )*
                while ( stream_ensures.hasNext() ) {
                    adaptor.addChild(root_1, stream_ensures.nextTree());

                }
                stream_ensures.reset();
                // src/edu/kit/iti/algover/parser/Pseudo.g:115:9: ( decreases )?
                if ( stream_decreases.hasNext() ) {
                    adaptor.addChild(root_1, stream_decreases.nextTree());

                }
                stream_decreases.reset();
                // src/edu/kit/iti/algover/parser/Pseudo.g:115:20: ( decl )*
                while ( stream_decl.hasNext() ) {
                    adaptor.addChild(root_1, stream_decl.nextTree());

                }
                stream_decl.reset();
                // src/edu/kit/iti/algover/parser/Pseudo.g:115:26: ^( BLOCK ( statements )? )
                {
                PseudoTree root_2 = (PseudoTree)adaptor.nil();
                root_2 = (PseudoTree)adaptor.becomeRoot((PseudoTree)adaptor.create(BLOCK, "BLOCK"), root_2);

                // src/edu/kit/iti/algover/parser/Pseudo.g:115:34: ( statements )?
                if ( stream_statements.hasNext() ) {
                    adaptor.addChild(root_2, stream_statements.nextTree());

                }
                stream_statements.reset();

                adaptor.addChild(root_1, root_2);
                }

                adaptor.addChild(root_0, root_1);
                }

            }

            retval.tree = root_0;}
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
        }
        return retval;
    }
    // $ANTLR end "method"

    public static class decl_return extends ParserRuleReturnScope {
        PseudoTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start "decl"
    // src/edu/kit/iti/algover/parser/Pseudo.g:118:1: decl : VAR var ';' ;
    public final PseudoParser.decl_return decl() throws RecognitionException {
        PseudoParser.decl_return retval = new PseudoParser.decl_return();
        retval.start = input.LT(1);

        PseudoTree root_0 = null;

        Token VAR15=null;
        Token char_literal17=null;
        PseudoParser.var_return var16 = null;


        PseudoTree VAR15_tree=null;
        PseudoTree char_literal17_tree=null;

        try {
            // src/edu/kit/iti/algover/parser/Pseudo.g:118:5: ( VAR var ';' )
            // src/edu/kit/iti/algover/parser/Pseudo.g:119:3: VAR var ';'
            {
            root_0 = (PseudoTree)adaptor.nil();

            VAR15=(Token)match(input,VAR,FOLLOW_VAR_in_decl548); if (state.failed) return retval;
            pushFollow(FOLLOW_var_in_decl551);
            var16=var();

            state._fsp--;
            if (state.failed) return retval;
            if ( state.backtracking==0 ) adaptor.addChild(root_0, var16.getTree());
            char_literal17=(Token)match(input,52,FOLLOW_52_in_decl553); if (state.failed) return retval;

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
        }
        return retval;
    }
    // $ANTLR end "decl"

    public static class vars_return extends ParserRuleReturnScope {
        PseudoTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start "vars"
    // src/edu/kit/iti/algover/parser/Pseudo.g:122:1: vars : var ( ',' var )* ;
    public final PseudoParser.vars_return vars() throws RecognitionException {
        PseudoParser.vars_return retval = new PseudoParser.vars_return();
        retval.start = input.LT(1);

        PseudoTree root_0 = null;

        Token char_literal19=null;
        PseudoParser.var_return var18 = null;

        PseudoParser.var_return var20 = null;


        PseudoTree char_literal19_tree=null;

        try {
            // src/edu/kit/iti/algover/parser/Pseudo.g:122:5: ( var ( ',' var )* )
            // src/edu/kit/iti/algover/parser/Pseudo.g:123:3: var ( ',' var )*
            {
            root_0 = (PseudoTree)adaptor.nil();

            pushFollow(FOLLOW_var_in_vars566);
            var18=var();

            state._fsp--;
            if (state.failed) return retval;
            if ( state.backtracking==0 ) adaptor.addChild(root_0, var18.getTree());
            // src/edu/kit/iti/algover/parser/Pseudo.g:124:3: ( ',' var )*
            loop9:
            do {
                int alt9=2;
                int LA9_0 = input.LA(1);

                if ( (LA9_0==53) ) {
                    alt9=1;
                }


                switch (alt9) {
            	case 1 :
            	    // src/edu/kit/iti/algover/parser/Pseudo.g:124:5: ',' var
            	    {
            	    char_literal19=(Token)match(input,53,FOLLOW_53_in_vars572); if (state.failed) return retval;
            	    pushFollow(FOLLOW_var_in_vars575);
            	    var20=var();

            	    state._fsp--;
            	    if (state.failed) return retval;
            	    if ( state.backtracking==0 ) adaptor.addChild(root_0, var20.getTree());

            	    }
            	    break;

            	default :
            	    break loop9;
                }
            } while (true);


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
        }
        return retval;
    }
    // $ANTLR end "vars"

    public static class var_return extends ParserRuleReturnScope {
        PseudoTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start "var"
    // src/edu/kit/iti/algover/parser/Pseudo.g:127:1: var : ID ':' type -> ^( VAR ID type ) ;
    public final PseudoParser.var_return var() throws RecognitionException {
        PseudoParser.var_return retval = new PseudoParser.var_return();
        retval.start = input.LT(1);

        PseudoTree root_0 = null;

        Token ID21=null;
        Token char_literal22=null;
        PseudoParser.type_return type23 = null;


        PseudoTree ID21_tree=null;
        PseudoTree char_literal22_tree=null;
        RewriteRuleTokenStream stream_ID=new RewriteRuleTokenStream(adaptor,"token ID");
        RewriteRuleTokenStream stream_54=new RewriteRuleTokenStream(adaptor,"token 54");
        RewriteRuleSubtreeStream stream_type=new RewriteRuleSubtreeStream(adaptor,"rule type");
        try {
            // src/edu/kit/iti/algover/parser/Pseudo.g:127:4: ( ID ':' type -> ^( VAR ID type ) )
            // src/edu/kit/iti/algover/parser/Pseudo.g:128:3: ID ':' type
            {
            ID21=(Token)match(input,ID,FOLLOW_ID_in_var590); if (state.failed) return retval; 
            if ( state.backtracking==0 ) stream_ID.add(ID21);

            char_literal22=(Token)match(input,54,FOLLOW_54_in_var592); if (state.failed) return retval; 
            if ( state.backtracking==0 ) stream_54.add(char_literal22);

            pushFollow(FOLLOW_type_in_var594);
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
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.tree:null);

            root_0 = (PseudoTree)adaptor.nil();
            // 128:15: -> ^( VAR ID type )
            {
                // src/edu/kit/iti/algover/parser/Pseudo.g:128:18: ^( VAR ID type )
                {
                PseudoTree root_1 = (PseudoTree)adaptor.nil();
                root_1 = (PseudoTree)adaptor.becomeRoot((PseudoTree)adaptor.create(VAR, "VAR"), root_1);

                adaptor.addChild(root_1, stream_ID.nextNode());
                adaptor.addChild(root_1, stream_type.nextTree());

                adaptor.addChild(root_0, root_1);
                }

            }

            retval.tree = root_0;}
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
        }
        return retval;
    }
    // $ANTLR end "var"

    public static class type_return extends ParserRuleReturnScope {
        PseudoTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start "type"
    // src/edu/kit/iti/algover/parser/Pseudo.g:131:1: type : ( INT | SET '<' INT '>' | ARRAY '<' INT '>' );
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
            // src/edu/kit/iti/algover/parser/Pseudo.g:131:5: ( INT | SET '<' INT '>' | ARRAY '<' INT '>' )
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
                    // src/edu/kit/iti/algover/parser/Pseudo.g:132:5: INT
                    {
                    root_0 = (PseudoTree)adaptor.nil();

                    INT24=(Token)match(input,INT,FOLLOW_INT_in_type618); if (state.failed) return retval;
                    if ( state.backtracking==0 ) {
                    INT24_tree = (PseudoTree)adaptor.create(INT24);
                    adaptor.addChild(root_0, INT24_tree);
                    }

                    }
                    break;
                case 2 :
                    // src/edu/kit/iti/algover/parser/Pseudo.g:132:11: SET '<' INT '>'
                    {
                    root_0 = (PseudoTree)adaptor.nil();

                    SET25=(Token)match(input,SET,FOLLOW_SET_in_type622); if (state.failed) return retval;
                    if ( state.backtracking==0 ) {
                    SET25_tree = (PseudoTree)adaptor.create(SET25);
                    root_0 = (PseudoTree)adaptor.becomeRoot(SET25_tree, root_0);
                    }
                    char_literal26=(Token)match(input,LT,FOLLOW_LT_in_type625); if (state.failed) return retval;
                    INT27=(Token)match(input,INT,FOLLOW_INT_in_type628); if (state.failed) return retval;
                    if ( state.backtracking==0 ) {
                    INT27_tree = (PseudoTree)adaptor.create(INT27);
                    adaptor.addChild(root_0, INT27_tree);
                    }
                    char_literal28=(Token)match(input,GT,FOLLOW_GT_in_type630); if (state.failed) return retval;

                    }
                    break;
                case 3 :
                    // src/edu/kit/iti/algover/parser/Pseudo.g:133:5: ARRAY '<' INT '>'
                    {
                    root_0 = (PseudoTree)adaptor.nil();

                    ARRAY29=(Token)match(input,ARRAY,FOLLOW_ARRAY_in_type637); if (state.failed) return retval;
                    if ( state.backtracking==0 ) {
                    ARRAY29_tree = (PseudoTree)adaptor.create(ARRAY29);
                    root_0 = (PseudoTree)adaptor.becomeRoot(ARRAY29_tree, root_0);
                    }
                    char_literal30=(Token)match(input,LT,FOLLOW_LT_in_type640); if (state.failed) return retval;
                    INT31=(Token)match(input,INT,FOLLOW_INT_in_type643); if (state.failed) return retval;
                    if ( state.backtracking==0 ) {
                    INT31_tree = (PseudoTree)adaptor.create(INT31);
                    adaptor.addChild(root_0, INT31_tree);
                    }
                    char_literal32=(Token)match(input,GT,FOLLOW_GT_in_type645); if (state.failed) return retval;

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
        }
        return retval;
    }
    // $ANTLR end "type"

    public static class returns__return extends ParserRuleReturnScope {
        PseudoTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start "returns_"
    // src/edu/kit/iti/algover/parser/Pseudo.g:136:1: returns_ : RETURNS '(' vars ')' ;
    public final PseudoParser.returns__return returns_() throws RecognitionException {
        PseudoParser.returns__return retval = new PseudoParser.returns__return();
        retval.start = input.LT(1);

        PseudoTree root_0 = null;

        Token RETURNS33=null;
        Token char_literal34=null;
        Token char_literal36=null;
        PseudoParser.vars_return vars35 = null;


        PseudoTree RETURNS33_tree=null;
        PseudoTree char_literal34_tree=null;
        PseudoTree char_literal36_tree=null;

        try {
            // src/edu/kit/iti/algover/parser/Pseudo.g:136:9: ( RETURNS '(' vars ')' )
            // src/edu/kit/iti/algover/parser/Pseudo.g:137:3: RETURNS '(' vars ')'
            {
            root_0 = (PseudoTree)adaptor.nil();

            RETURNS33=(Token)match(input,RETURNS,FOLLOW_RETURNS_in_returns_658); if (state.failed) return retval;
            if ( state.backtracking==0 ) {
            RETURNS33_tree = (PseudoTree)adaptor.create(RETURNS33);
            root_0 = (PseudoTree)adaptor.becomeRoot(RETURNS33_tree, root_0);
            }
            char_literal34=(Token)match(input,50,FOLLOW_50_in_returns_661); if (state.failed) return retval;
            pushFollow(FOLLOW_vars_in_returns_664);
            vars35=vars();

            state._fsp--;
            if (state.failed) return retval;
            if ( state.backtracking==0 ) adaptor.addChild(root_0, vars35.getTree());
            char_literal36=(Token)match(input,51,FOLLOW_51_in_returns_666); if (state.failed) return retval;

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
        }
        return retval;
    }
    // $ANTLR end "returns_"

    public static class requires_return extends ParserRuleReturnScope {
        PseudoTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start "requires"
    // src/edu/kit/iti/algover/parser/Pseudo.g:140:1: requires : REQUIRES ( ID ':' )? expression ;
    public final PseudoParser.requires_return requires() throws RecognitionException {
        PseudoParser.requires_return retval = new PseudoParser.requires_return();
        retval.start = input.LT(1);

        PseudoTree root_0 = null;

        Token REQUIRES37=null;
        Token ID38=null;
        Token char_literal39=null;
        PseudoParser.expression_return expression40 = null;


        PseudoTree REQUIRES37_tree=null;
        PseudoTree ID38_tree=null;
        PseudoTree char_literal39_tree=null;

        try {
            // src/edu/kit/iti/algover/parser/Pseudo.g:140:9: ( REQUIRES ( ID ':' )? expression )
            // src/edu/kit/iti/algover/parser/Pseudo.g:141:3: REQUIRES ( ID ':' )? expression
            {
            root_0 = (PseudoTree)adaptor.nil();

            REQUIRES37=(Token)match(input,REQUIRES,FOLLOW_REQUIRES_in_requires679); if (state.failed) return retval;
            if ( state.backtracking==0 ) {
            REQUIRES37_tree = (PseudoTree)adaptor.create(REQUIRES37);
            root_0 = (PseudoTree)adaptor.becomeRoot(REQUIRES37_tree, root_0);
            }
            // src/edu/kit/iti/algover/parser/Pseudo.g:141:13: ( ID ':' )?
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
                    // src/edu/kit/iti/algover/parser/Pseudo.g:141:14: ID ':'
                    {
                    ID38=(Token)match(input,ID,FOLLOW_ID_in_requires683); if (state.failed) return retval;
                    if ( state.backtracking==0 ) {
                    ID38_tree = (PseudoTree)adaptor.create(ID38);
                    adaptor.addChild(root_0, ID38_tree);
                    }
                    char_literal39=(Token)match(input,54,FOLLOW_54_in_requires685); if (state.failed) return retval;

                    }
                    break;

            }

            pushFollow(FOLLOW_expression_in_requires690);
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
        }
        return retval;
    }
    // $ANTLR end "requires"

    public static class ensures_return extends ParserRuleReturnScope {
        PseudoTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start "ensures"
    // src/edu/kit/iti/algover/parser/Pseudo.g:144:1: ensures : ENSURES ( ID ':' )? expression ;
    public final PseudoParser.ensures_return ensures() throws RecognitionException {
        PseudoParser.ensures_return retval = new PseudoParser.ensures_return();
        retval.start = input.LT(1);

        PseudoTree root_0 = null;

        Token ENSURES41=null;
        Token ID42=null;
        Token char_literal43=null;
        PseudoParser.expression_return expression44 = null;


        PseudoTree ENSURES41_tree=null;
        PseudoTree ID42_tree=null;
        PseudoTree char_literal43_tree=null;

        try {
            // src/edu/kit/iti/algover/parser/Pseudo.g:144:8: ( ENSURES ( ID ':' )? expression )
            // src/edu/kit/iti/algover/parser/Pseudo.g:145:3: ENSURES ( ID ':' )? expression
            {
            root_0 = (PseudoTree)adaptor.nil();

            ENSURES41=(Token)match(input,ENSURES,FOLLOW_ENSURES_in_ensures702); if (state.failed) return retval;
            if ( state.backtracking==0 ) {
            ENSURES41_tree = (PseudoTree)adaptor.create(ENSURES41);
            root_0 = (PseudoTree)adaptor.becomeRoot(ENSURES41_tree, root_0);
            }
            // src/edu/kit/iti/algover/parser/Pseudo.g:145:12: ( ID ':' )?
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
                    // src/edu/kit/iti/algover/parser/Pseudo.g:145:13: ID ':'
                    {
                    ID42=(Token)match(input,ID,FOLLOW_ID_in_ensures706); if (state.failed) return retval;
                    if ( state.backtracking==0 ) {
                    ID42_tree = (PseudoTree)adaptor.create(ID42);
                    adaptor.addChild(root_0, ID42_tree);
                    }
                    char_literal43=(Token)match(input,54,FOLLOW_54_in_ensures708); if (state.failed) return retval;

                    }
                    break;

            }

            pushFollow(FOLLOW_expression_in_ensures713);
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
        }
        return retval;
    }
    // $ANTLR end "ensures"

    public static class decreases_return extends ParserRuleReturnScope {
        PseudoTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start "decreases"
    // src/edu/kit/iti/algover/parser/Pseudo.g:148:1: decreases : DECREASES expression ;
    public final PseudoParser.decreases_return decreases() throws RecognitionException {
        PseudoParser.decreases_return retval = new PseudoParser.decreases_return();
        retval.start = input.LT(1);

        PseudoTree root_0 = null;

        Token DECREASES45=null;
        PseudoParser.expression_return expression46 = null;


        PseudoTree DECREASES45_tree=null;

        try {
            // src/edu/kit/iti/algover/parser/Pseudo.g:148:10: ( DECREASES expression )
            // src/edu/kit/iti/algover/parser/Pseudo.g:149:3: DECREASES expression
            {
            root_0 = (PseudoTree)adaptor.nil();

            DECREASES45=(Token)match(input,DECREASES,FOLLOW_DECREASES_in_decreases725); if (state.failed) return retval;
            if ( state.backtracking==0 ) {
            DECREASES45_tree = (PseudoTree)adaptor.create(DECREASES45);
            root_0 = (PseudoTree)adaptor.becomeRoot(DECREASES45_tree, root_0);
            }
            pushFollow(FOLLOW_expression_in_decreases728);
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
        }
        return retval;
    }
    // $ANTLR end "decreases"

    public static class invariant_return extends ParserRuleReturnScope {
        PseudoTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start "invariant"
    // src/edu/kit/iti/algover/parser/Pseudo.g:152:1: invariant : INVARIANT ( ID ':' )? expression ;
    public final PseudoParser.invariant_return invariant() throws RecognitionException {
        PseudoParser.invariant_return retval = new PseudoParser.invariant_return();
        retval.start = input.LT(1);

        PseudoTree root_0 = null;

        Token INVARIANT47=null;
        Token ID48=null;
        Token char_literal49=null;
        PseudoParser.expression_return expression50 = null;


        PseudoTree INVARIANT47_tree=null;
        PseudoTree ID48_tree=null;
        PseudoTree char_literal49_tree=null;

        try {
            // src/edu/kit/iti/algover/parser/Pseudo.g:152:10: ( INVARIANT ( ID ':' )? expression )
            // src/edu/kit/iti/algover/parser/Pseudo.g:153:3: INVARIANT ( ID ':' )? expression
            {
            root_0 = (PseudoTree)adaptor.nil();

            INVARIANT47=(Token)match(input,INVARIANT,FOLLOW_INVARIANT_in_invariant740); if (state.failed) return retval;
            if ( state.backtracking==0 ) {
            INVARIANT47_tree = (PseudoTree)adaptor.create(INVARIANT47);
            root_0 = (PseudoTree)adaptor.becomeRoot(INVARIANT47_tree, root_0);
            }
            // src/edu/kit/iti/algover/parser/Pseudo.g:153:14: ( ID ':' )?
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
                    // src/edu/kit/iti/algover/parser/Pseudo.g:153:15: ID ':'
                    {
                    ID48=(Token)match(input,ID,FOLLOW_ID_in_invariant744); if (state.failed) return retval;
                    if ( state.backtracking==0 ) {
                    ID48_tree = (PseudoTree)adaptor.create(ID48);
                    adaptor.addChild(root_0, ID48_tree);
                    }
                    char_literal49=(Token)match(input,54,FOLLOW_54_in_invariant746); if (state.failed) return retval;

                    }
                    break;

            }

            pushFollow(FOLLOW_expression_in_invariant751);
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
        }
        return retval;
    }
    // $ANTLR end "invariant"

    public static class block_return extends ParserRuleReturnScope {
        PseudoTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start "block"
    // src/edu/kit/iti/algover/parser/Pseudo.g:156:1: block : '{' ( statements )? '}' -> ^( BLOCK ( statements )? ) ;
    public final PseudoParser.block_return block() throws RecognitionException {
        PseudoParser.block_return retval = new PseudoParser.block_return();
        retval.start = input.LT(1);

        PseudoTree root_0 = null;

        Token char_literal51=null;
        Token char_literal53=null;
        PseudoParser.statements_return statements52 = null;


        PseudoTree char_literal51_tree=null;
        PseudoTree char_literal53_tree=null;
        RewriteRuleTokenStream stream_BLOCK_BEGIN=new RewriteRuleTokenStream(adaptor,"token BLOCK_BEGIN");
        RewriteRuleTokenStream stream_BLOCK_END=new RewriteRuleTokenStream(adaptor,"token BLOCK_END");
        RewriteRuleSubtreeStream stream_statements=new RewriteRuleSubtreeStream(adaptor,"rule statements");
        try {
            // src/edu/kit/iti/algover/parser/Pseudo.g:156:6: ( '{' ( statements )? '}' -> ^( BLOCK ( statements )? ) )
            // src/edu/kit/iti/algover/parser/Pseudo.g:157:3: '{' ( statements )? '}'
            {
            char_literal51=(Token)match(input,BLOCK_BEGIN,FOLLOW_BLOCK_BEGIN_in_block763); if (state.failed) return retval; 
            if ( state.backtracking==0 ) stream_BLOCK_BEGIN.add(char_literal51);

            // src/edu/kit/iti/algover/parser/Pseudo.g:157:7: ( statements )?
            int alt14=2;
            int LA14_0 = input.LA(1);

            if ( (LA14_0==IF||LA14_0==WHILE||LA14_0==ASSERT||LA14_0==ID||LA14_0==55) ) {
                alt14=1;
            }
            switch (alt14) {
                case 1 :
                    // src/edu/kit/iti/algover/parser/Pseudo.g:157:7: statements
                    {
                    pushFollow(FOLLOW_statements_in_block765);
                    statements52=statements();

                    state._fsp--;
                    if (state.failed) return retval;
                    if ( state.backtracking==0 ) stream_statements.add(statements52.getTree());

                    }
                    break;

            }

            char_literal53=(Token)match(input,BLOCK_END,FOLLOW_BLOCK_END_in_block768); if (state.failed) return retval; 
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
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.tree:null);

            root_0 = (PseudoTree)adaptor.nil();
            // 157:23: -> ^( BLOCK ( statements )? )
            {
                // src/edu/kit/iti/algover/parser/Pseudo.g:157:26: ^( BLOCK ( statements )? )
                {
                PseudoTree root_1 = (PseudoTree)adaptor.nil();
                root_1 = (PseudoTree)adaptor.becomeRoot((PseudoTree)adaptor.create(BLOCK, "BLOCK"), root_1);

                // src/edu/kit/iti/algover/parser/Pseudo.g:157:34: ( statements )?
                if ( stream_statements.hasNext() ) {
                    adaptor.addChild(root_1, stream_statements.nextTree());

                }
                stream_statements.reset();

                adaptor.addChild(root_0, root_1);
                }

            }

            retval.tree = root_0;}
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
        }
        return retval;
    }
    // $ANTLR end "block"

    public static class relaxedBlock_return extends ParserRuleReturnScope {
        PseudoTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start "relaxedBlock"
    // src/edu/kit/iti/algover/parser/Pseudo.g:160:1: relaxedBlock : ( block | statement -> ^( BLOCK statement ) );
    public final PseudoParser.relaxedBlock_return relaxedBlock() throws RecognitionException {
        PseudoParser.relaxedBlock_return retval = new PseudoParser.relaxedBlock_return();
        retval.start = input.LT(1);

        PseudoTree root_0 = null;

        PseudoParser.block_return block54 = null;

        PseudoParser.statement_return statement55 = null;


        RewriteRuleSubtreeStream stream_statement=new RewriteRuleSubtreeStream(adaptor,"rule statement");
        try {
            // src/edu/kit/iti/algover/parser/Pseudo.g:160:13: ( block | statement -> ^( BLOCK statement ) )
            int alt15=2;
            int LA15_0 = input.LA(1);

            if ( (LA15_0==BLOCK_BEGIN) ) {
                alt15=1;
            }
            else if ( (LA15_0==IF||LA15_0==WHILE||LA15_0==ASSERT||LA15_0==ID||LA15_0==55) ) {
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
                    // src/edu/kit/iti/algover/parser/Pseudo.g:161:5: block
                    {
                    root_0 = (PseudoTree)adaptor.nil();

                    pushFollow(FOLLOW_block_in_relaxedBlock791);
                    block54=block();

                    state._fsp--;
                    if (state.failed) return retval;
                    if ( state.backtracking==0 ) adaptor.addChild(root_0, block54.getTree());

                    }
                    break;
                case 2 :
                    // src/edu/kit/iti/algover/parser/Pseudo.g:162:5: statement
                    {
                    pushFollow(FOLLOW_statement_in_relaxedBlock797);
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
                    RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.tree:null);

                    root_0 = (PseudoTree)adaptor.nil();
                    // 162:15: -> ^( BLOCK statement )
                    {
                        // src/edu/kit/iti/algover/parser/Pseudo.g:162:18: ^( BLOCK statement )
                        {
                        PseudoTree root_1 = (PseudoTree)adaptor.nil();
                        root_1 = (PseudoTree)adaptor.becomeRoot((PseudoTree)adaptor.create(BLOCK, "BLOCK"), root_1);

                        adaptor.addChild(root_1, stream_statement.nextTree());

                        adaptor.addChild(root_0, root_1);
                        }

                    }

                    retval.tree = root_0;}
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
        }
        return retval;
    }
    // $ANTLR end "relaxedBlock"

    public static class statements_return extends ParserRuleReturnScope {
        PseudoTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start "statements"
    // src/edu/kit/iti/algover/parser/Pseudo.g:165:1: statements : ( statement )+ ;
    public final PseudoParser.statements_return statements() throws RecognitionException {
        PseudoParser.statements_return retval = new PseudoParser.statements_return();
        retval.start = input.LT(1);

        PseudoTree root_0 = null;

        PseudoParser.statement_return statement56 = null;



        try {
            // src/edu/kit/iti/algover/parser/Pseudo.g:165:11: ( ( statement )+ )
            // src/edu/kit/iti/algover/parser/Pseudo.g:166:3: ( statement )+
            {
            root_0 = (PseudoTree)adaptor.nil();

            // src/edu/kit/iti/algover/parser/Pseudo.g:166:3: ( statement )+
            int cnt16=0;
            loop16:
            do {
                int alt16=2;
                int LA16_0 = input.LA(1);

                if ( (LA16_0==IF||LA16_0==WHILE||LA16_0==ASSERT||LA16_0==ID||LA16_0==55) ) {
                    alt16=1;
                }


                switch (alt16) {
            	case 1 :
            	    // src/edu/kit/iti/algover/parser/Pseudo.g:166:5: statement
            	    {
            	    pushFollow(FOLLOW_statement_in_statements819);
            	    statement56=statement();

            	    state._fsp--;
            	    if (state.failed) return retval;
            	    if ( state.backtracking==0 ) adaptor.addChild(root_0, statement56.getTree());

            	    }
            	    break;

            	default :
            	    if ( cnt16 >= 1 ) break loop16;
            	    if (state.backtracking>0) {state.failed=true; return retval;}
                        EarlyExitException eee =
                            new EarlyExitException(16, input);
                        throw eee;
                }
                cnt16++;
            } while (true);


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
        }
        return retval;
    }
    // $ANTLR end "statements"

    public static class statement_return extends ParserRuleReturnScope {
        PseudoTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start "statement"
    // src/edu/kit/iti/algover/parser/Pseudo.g:169:1: statement : ( ID ':=' expression ';' | ( ID ':=' 'call' )=>r= ID ':=' 'call' f= ID '(' ( expressions )? ')' ';' -> ^( 'call' $f ^( RESULTS $r) ^( ARGS ( expressions )? ) ) | ids ':=' 'call' ID '(' ( expressions )? ')' ';' -> ^( 'call' ID ^( RESULTS ids ) ^( ARGS ( expressions )? ) ) | 'while' expression ( invariant )+ decreases relaxedBlock | 'if' expression relaxedBlock ( options {greedy=true; } : 'else' relaxedBlock )? | 'assert' ( ID ':' )? expression ';' | 'assume' ( ID ':' )? expression ';' );
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
        Token string_literal90=null;
        Token ID91=null;
        Token char_literal92=null;
        Token char_literal94=null;
        PseudoParser.expression_return expression59 = null;

        PseudoParser.expressions_return expressions64 = null;

        PseudoParser.ids_return ids67 = null;

        PseudoParser.expressions_return expressions72 = null;

        PseudoParser.expression_return expression76 = null;

        PseudoParser.invariant_return invariant77 = null;

        PseudoParser.decreases_return decreases78 = null;

        PseudoParser.relaxedBlock_return relaxedBlock79 = null;

        PseudoParser.expression_return expression81 = null;

        PseudoParser.relaxedBlock_return relaxedBlock82 = null;

        PseudoParser.relaxedBlock_return relaxedBlock84 = null;

        PseudoParser.expression_return expression88 = null;

        PseudoParser.expression_return expression93 = null;


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
        PseudoTree string_literal90_tree=null;
        PseudoTree ID91_tree=null;
        PseudoTree char_literal92_tree=null;
        PseudoTree char_literal94_tree=null;
        RewriteRuleTokenStream stream_CALL=new RewriteRuleTokenStream(adaptor,"token CALL");
        RewriteRuleTokenStream stream_51=new RewriteRuleTokenStream(adaptor,"token 51");
        RewriteRuleTokenStream stream_ID=new RewriteRuleTokenStream(adaptor,"token ID");
        RewriteRuleTokenStream stream_52=new RewriteRuleTokenStream(adaptor,"token 52");
        RewriteRuleTokenStream stream_ASSIGN=new RewriteRuleTokenStream(adaptor,"token ASSIGN");
        RewriteRuleTokenStream stream_50=new RewriteRuleTokenStream(adaptor,"token 50");
        RewriteRuleSubtreeStream stream_ids=new RewriteRuleSubtreeStream(adaptor,"rule ids");
        RewriteRuleSubtreeStream stream_expressions=new RewriteRuleSubtreeStream(adaptor,"rule expressions");
        try {
            // src/edu/kit/iti/algover/parser/Pseudo.g:169:10: ( ID ':=' expression ';' | ( ID ':=' 'call' )=>r= ID ':=' 'call' f= ID '(' ( expressions )? ')' ';' -> ^( 'call' $f ^( RESULTS $r) ^( ARGS ( expressions )? ) ) | ids ':=' 'call' ID '(' ( expressions )? ')' ';' -> ^( 'call' ID ^( RESULTS ids ) ^( ARGS ( expressions )? ) ) | 'while' expression ( invariant )+ decreases relaxedBlock | 'if' expression relaxedBlock ( options {greedy=true; } : 'else' relaxedBlock )? | 'assert' ( ID ':' )? expression ';' | 'assume' ( ID ':' )? expression ';' )
            int alt23=7;
            alt23 = dfa23.predict(input);
            switch (alt23) {
                case 1 :
                    // src/edu/kit/iti/algover/parser/Pseudo.g:170:5: ID ':=' expression ';'
                    {
                    root_0 = (PseudoTree)adaptor.nil();

                    ID57=(Token)match(input,ID,FOLLOW_ID_in_statement836); if (state.failed) return retval;
                    if ( state.backtracking==0 ) {
                    ID57_tree = (PseudoTree)adaptor.create(ID57);
                    adaptor.addChild(root_0, ID57_tree);
                    }
                    string_literal58=(Token)match(input,ASSIGN,FOLLOW_ASSIGN_in_statement838); if (state.failed) return retval;
                    if ( state.backtracking==0 ) {
                    string_literal58_tree = (PseudoTree)adaptor.create(string_literal58);
                    root_0 = (PseudoTree)adaptor.becomeRoot(string_literal58_tree, root_0);
                    }
                    pushFollow(FOLLOW_expression_in_statement841);
                    expression59=expression();

                    state._fsp--;
                    if (state.failed) return retval;
                    if ( state.backtracking==0 ) adaptor.addChild(root_0, expression59.getTree());
                    char_literal60=(Token)match(input,52,FOLLOW_52_in_statement843); if (state.failed) return retval;

                    }
                    break;
                case 2 :
                    // src/edu/kit/iti/algover/parser/Pseudo.g:171:5: ( ID ':=' 'call' )=>r= ID ':=' 'call' f= ID '(' ( expressions )? ')' ';'
                    {
                    r=(Token)match(input,ID,FOLLOW_ID_in_statement862); if (state.failed) return retval; 
                    if ( state.backtracking==0 ) stream_ID.add(r);

                    string_literal61=(Token)match(input,ASSIGN,FOLLOW_ASSIGN_in_statement864); if (state.failed) return retval; 
                    if ( state.backtracking==0 ) stream_ASSIGN.add(string_literal61);

                    string_literal62=(Token)match(input,CALL,FOLLOW_CALL_in_statement866); if (state.failed) return retval; 
                    if ( state.backtracking==0 ) stream_CALL.add(string_literal62);

                    f=(Token)match(input,ID,FOLLOW_ID_in_statement870); if (state.failed) return retval; 
                    if ( state.backtracking==0 ) stream_ID.add(f);

                    char_literal63=(Token)match(input,50,FOLLOW_50_in_statement872); if (state.failed) return retval; 
                    if ( state.backtracking==0 ) stream_50.add(char_literal63);

                    // src/edu/kit/iti/algover/parser/Pseudo.g:171:51: ( expressions )?
                    int alt17=2;
                    int LA17_0 = input.LA(1);

                    if ( ((LA17_0>=MINUS && LA17_0<=NOT)||LA17_0==BLOCK_BEGIN||(LA17_0>=ID && LA17_0<=LIT)||LA17_0==50||LA17_0==56) ) {
                        alt17=1;
                    }
                    switch (alt17) {
                        case 1 :
                            // src/edu/kit/iti/algover/parser/Pseudo.g:171:51: expressions
                            {
                            pushFollow(FOLLOW_expressions_in_statement874);
                            expressions64=expressions();

                            state._fsp--;
                            if (state.failed) return retval;
                            if ( state.backtracking==0 ) stream_expressions.add(expressions64.getTree());

                            }
                            break;

                    }

                    char_literal65=(Token)match(input,51,FOLLOW_51_in_statement877); if (state.failed) return retval; 
                    if ( state.backtracking==0 ) stream_51.add(char_literal65);

                    char_literal66=(Token)match(input,52,FOLLOW_52_in_statement879); if (state.failed) return retval; 
                    if ( state.backtracking==0 ) stream_52.add(char_literal66);



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
                    RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.tree:null);

                    root_0 = (PseudoTree)adaptor.nil();
                    // 172:9: -> ^( 'call' $f ^( RESULTS $r) ^( ARGS ( expressions )? ) )
                    {
                        // src/edu/kit/iti/algover/parser/Pseudo.g:172:12: ^( 'call' $f ^( RESULTS $r) ^( ARGS ( expressions )? ) )
                        {
                        PseudoTree root_1 = (PseudoTree)adaptor.nil();
                        root_1 = (PseudoTree)adaptor.becomeRoot(stream_CALL.nextNode(), root_1);

                        adaptor.addChild(root_1, stream_f.nextNode());
                        // src/edu/kit/iti/algover/parser/Pseudo.g:172:24: ^( RESULTS $r)
                        {
                        PseudoTree root_2 = (PseudoTree)adaptor.nil();
                        root_2 = (PseudoTree)adaptor.becomeRoot((PseudoTree)adaptor.create(RESULTS, "RESULTS"), root_2);

                        adaptor.addChild(root_2, stream_r.nextNode());

                        adaptor.addChild(root_1, root_2);
                        }
                        // src/edu/kit/iti/algover/parser/Pseudo.g:172:38: ^( ARGS ( expressions )? )
                        {
                        PseudoTree root_2 = (PseudoTree)adaptor.nil();
                        root_2 = (PseudoTree)adaptor.becomeRoot((PseudoTree)adaptor.create(ARGS, "ARGS"), root_2);

                        // src/edu/kit/iti/algover/parser/Pseudo.g:172:45: ( expressions )?
                        if ( stream_expressions.hasNext() ) {
                            adaptor.addChild(root_2, stream_expressions.nextTree());

                        }
                        stream_expressions.reset();

                        adaptor.addChild(root_1, root_2);
                        }

                        adaptor.addChild(root_0, root_1);
                        }

                    }

                    retval.tree = root_0;}
                    }
                    break;
                case 3 :
                    // src/edu/kit/iti/algover/parser/Pseudo.g:173:5: ids ':=' 'call' ID '(' ( expressions )? ')' ';'
                    {
                    pushFollow(FOLLOW_ids_in_statement916);
                    ids67=ids();

                    state._fsp--;
                    if (state.failed) return retval;
                    if ( state.backtracking==0 ) stream_ids.add(ids67.getTree());
                    string_literal68=(Token)match(input,ASSIGN,FOLLOW_ASSIGN_in_statement918); if (state.failed) return retval; 
                    if ( state.backtracking==0 ) stream_ASSIGN.add(string_literal68);

                    string_literal69=(Token)match(input,CALL,FOLLOW_CALL_in_statement920); if (state.failed) return retval; 
                    if ( state.backtracking==0 ) stream_CALL.add(string_literal69);

                    ID70=(Token)match(input,ID,FOLLOW_ID_in_statement922); if (state.failed) return retval; 
                    if ( state.backtracking==0 ) stream_ID.add(ID70);

                    char_literal71=(Token)match(input,50,FOLLOW_50_in_statement924); if (state.failed) return retval; 
                    if ( state.backtracking==0 ) stream_50.add(char_literal71);

                    // src/edu/kit/iti/algover/parser/Pseudo.g:173:28: ( expressions )?
                    int alt18=2;
                    int LA18_0 = input.LA(1);

                    if ( ((LA18_0>=MINUS && LA18_0<=NOT)||LA18_0==BLOCK_BEGIN||(LA18_0>=ID && LA18_0<=LIT)||LA18_0==50||LA18_0==56) ) {
                        alt18=1;
                    }
                    switch (alt18) {
                        case 1 :
                            // src/edu/kit/iti/algover/parser/Pseudo.g:173:28: expressions
                            {
                            pushFollow(FOLLOW_expressions_in_statement926);
                            expressions72=expressions();

                            state._fsp--;
                            if (state.failed) return retval;
                            if ( state.backtracking==0 ) stream_expressions.add(expressions72.getTree());

                            }
                            break;

                    }

                    char_literal73=(Token)match(input,51,FOLLOW_51_in_statement929); if (state.failed) return retval; 
                    if ( state.backtracking==0 ) stream_51.add(char_literal73);

                    char_literal74=(Token)match(input,52,FOLLOW_52_in_statement931); if (state.failed) return retval; 
                    if ( state.backtracking==0 ) stream_52.add(char_literal74);



                    // AST REWRITE
                    // elements: ids, CALL, ID, expressions
                    // token labels: 
                    // rule labels: retval
                    // token list labels: 
                    // rule list labels: 
                    // wildcard labels: 
                    if ( state.backtracking==0 ) {
                    retval.tree = root_0;
                    RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.tree:null);

                    root_0 = (PseudoTree)adaptor.nil();
                    // 174:9: -> ^( 'call' ID ^( RESULTS ids ) ^( ARGS ( expressions )? ) )
                    {
                        // src/edu/kit/iti/algover/parser/Pseudo.g:174:12: ^( 'call' ID ^( RESULTS ids ) ^( ARGS ( expressions )? ) )
                        {
                        PseudoTree root_1 = (PseudoTree)adaptor.nil();
                        root_1 = (PseudoTree)adaptor.becomeRoot(stream_CALL.nextNode(), root_1);

                        adaptor.addChild(root_1, stream_ID.nextNode());
                        // src/edu/kit/iti/algover/parser/Pseudo.g:174:24: ^( RESULTS ids )
                        {
                        PseudoTree root_2 = (PseudoTree)adaptor.nil();
                        root_2 = (PseudoTree)adaptor.becomeRoot((PseudoTree)adaptor.create(RESULTS, "RESULTS"), root_2);

                        adaptor.addChild(root_2, stream_ids.nextTree());

                        adaptor.addChild(root_1, root_2);
                        }
                        // src/edu/kit/iti/algover/parser/Pseudo.g:174:39: ^( ARGS ( expressions )? )
                        {
                        PseudoTree root_2 = (PseudoTree)adaptor.nil();
                        root_2 = (PseudoTree)adaptor.becomeRoot((PseudoTree)adaptor.create(ARGS, "ARGS"), root_2);

                        // src/edu/kit/iti/algover/parser/Pseudo.g:174:46: ( expressions )?
                        if ( stream_expressions.hasNext() ) {
                            adaptor.addChild(root_2, stream_expressions.nextTree());

                        }
                        stream_expressions.reset();

                        adaptor.addChild(root_1, root_2);
                        }

                        adaptor.addChild(root_0, root_1);
                        }

                    }

                    retval.tree = root_0;}
                    }
                    break;
                case 4 :
                    // src/edu/kit/iti/algover/parser/Pseudo.g:175:5: 'while' expression ( invariant )+ decreases relaxedBlock
                    {
                    root_0 = (PseudoTree)adaptor.nil();

                    string_literal75=(Token)match(input,WHILE,FOLLOW_WHILE_in_statement966); if (state.failed) return retval;
                    if ( state.backtracking==0 ) {
                    string_literal75_tree = (PseudoTree)adaptor.create(string_literal75);
                    root_0 = (PseudoTree)adaptor.becomeRoot(string_literal75_tree, root_0);
                    }
                    pushFollow(FOLLOW_expression_in_statement969);
                    expression76=expression();

                    state._fsp--;
                    if (state.failed) return retval;
                    if ( state.backtracking==0 ) adaptor.addChild(root_0, expression76.getTree());
                    // src/edu/kit/iti/algover/parser/Pseudo.g:176:7: ( invariant )+
                    int cnt19=0;
                    loop19:
                    do {
                        int alt19=2;
                        int LA19_0 = input.LA(1);

                        if ( (LA19_0==INVARIANT) ) {
                            alt19=1;
                        }


                        switch (alt19) {
                    	case 1 :
                    	    // src/edu/kit/iti/algover/parser/Pseudo.g:176:7: invariant
                    	    {
                    	    pushFollow(FOLLOW_invariant_in_statement977);
                    	    invariant77=invariant();

                    	    state._fsp--;
                    	    if (state.failed) return retval;
                    	    if ( state.backtracking==0 ) adaptor.addChild(root_0, invariant77.getTree());

                    	    }
                    	    break;

                    	default :
                    	    if ( cnt19 >= 1 ) break loop19;
                    	    if (state.backtracking>0) {state.failed=true; return retval;}
                                EarlyExitException eee =
                                    new EarlyExitException(19, input);
                                throw eee;
                        }
                        cnt19++;
                    } while (true);

                    pushFollow(FOLLOW_decreases_in_statement986);
                    decreases78=decreases();

                    state._fsp--;
                    if (state.failed) return retval;
                    if ( state.backtracking==0 ) adaptor.addChild(root_0, decreases78.getTree());
                    pushFollow(FOLLOW_relaxedBlock_in_statement994);
                    relaxedBlock79=relaxedBlock();

                    state._fsp--;
                    if (state.failed) return retval;
                    if ( state.backtracking==0 ) adaptor.addChild(root_0, relaxedBlock79.getTree());

                    }
                    break;
                case 5 :
                    // src/edu/kit/iti/algover/parser/Pseudo.g:179:5: 'if' expression relaxedBlock ( options {greedy=true; } : 'else' relaxedBlock )?
                    {
                    root_0 = (PseudoTree)adaptor.nil();

                    string_literal80=(Token)match(input,IF,FOLLOW_IF_in_statement1000); if (state.failed) return retval;
                    if ( state.backtracking==0 ) {
                    string_literal80_tree = (PseudoTree)adaptor.create(string_literal80);
                    root_0 = (PseudoTree)adaptor.becomeRoot(string_literal80_tree, root_0);
                    }
                    pushFollow(FOLLOW_expression_in_statement1003);
                    expression81=expression();

                    state._fsp--;
                    if (state.failed) return retval;
                    if ( state.backtracking==0 ) adaptor.addChild(root_0, expression81.getTree());
                    pushFollow(FOLLOW_relaxedBlock_in_statement1005);
                    relaxedBlock82=relaxedBlock();

                    state._fsp--;
                    if (state.failed) return retval;
                    if ( state.backtracking==0 ) adaptor.addChild(root_0, relaxedBlock82.getTree());
                    // src/edu/kit/iti/algover/parser/Pseudo.g:180:7: ( options {greedy=true; } : 'else' relaxedBlock )?
                    int alt20=2;
                    int LA20_0 = input.LA(1);

                    if ( (LA20_0==ELSE) ) {
                        alt20=1;
                    }
                    switch (alt20) {
                        case 1 :
                            // src/edu/kit/iti/algover/parser/Pseudo.g:180:36: 'else' relaxedBlock
                            {
                            string_literal83=(Token)match(input,ELSE,FOLLOW_ELSE_in_statement1026); if (state.failed) return retval;
                            pushFollow(FOLLOW_relaxedBlock_in_statement1029);
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
                    // src/edu/kit/iti/algover/parser/Pseudo.g:181:5: 'assert' ( ID ':' )? expression ';'
                    {
                    root_0 = (PseudoTree)adaptor.nil();

                    string_literal85=(Token)match(input,ASSERT,FOLLOW_ASSERT_in_statement1038); if (state.failed) return retval;
                    if ( state.backtracking==0 ) {
                    string_literal85_tree = (PseudoTree)adaptor.create(string_literal85);
                    root_0 = (PseudoTree)adaptor.becomeRoot(string_literal85_tree, root_0);
                    }
                    // src/edu/kit/iti/algover/parser/Pseudo.g:181:15: ( ID ':' )?
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
                            // src/edu/kit/iti/algover/parser/Pseudo.g:181:17: ID ':'
                            {
                            ID86=(Token)match(input,ID,FOLLOW_ID_in_statement1043); if (state.failed) return retval;
                            if ( state.backtracking==0 ) {
                            ID86_tree = (PseudoTree)adaptor.create(ID86);
                            adaptor.addChild(root_0, ID86_tree);
                            }
                            char_literal87=(Token)match(input,54,FOLLOW_54_in_statement1045); if (state.failed) return retval;

                            }
                            break;

                    }

                    pushFollow(FOLLOW_expression_in_statement1051);
                    expression88=expression();

                    state._fsp--;
                    if (state.failed) return retval;
                    if ( state.backtracking==0 ) adaptor.addChild(root_0, expression88.getTree());
                    char_literal89=(Token)match(input,52,FOLLOW_52_in_statement1053); if (state.failed) return retval;

                    }
                    break;
                case 7 :
                    // src/edu/kit/iti/algover/parser/Pseudo.g:182:5: 'assume' ( ID ':' )? expression ';'
                    {
                    root_0 = (PseudoTree)adaptor.nil();

                    string_literal90=(Token)match(input,55,FOLLOW_55_in_statement1060); if (state.failed) return retval;
                    if ( state.backtracking==0 ) {
                    string_literal90_tree = (PseudoTree)adaptor.create(string_literal90);
                    root_0 = (PseudoTree)adaptor.becomeRoot(string_literal90_tree, root_0);
                    }
                    // src/edu/kit/iti/algover/parser/Pseudo.g:182:15: ( ID ':' )?
                    int alt22=2;
                    int LA22_0 = input.LA(1);

                    if ( (LA22_0==ID) ) {
                        int LA22_1 = input.LA(2);

                        if ( (LA22_1==54) ) {
                            alt22=1;
                        }
                    }
                    switch (alt22) {
                        case 1 :
                            // src/edu/kit/iti/algover/parser/Pseudo.g:182:17: ID ':'
                            {
                            ID91=(Token)match(input,ID,FOLLOW_ID_in_statement1065); if (state.failed) return retval;
                            if ( state.backtracking==0 ) {
                            ID91_tree = (PseudoTree)adaptor.create(ID91);
                            adaptor.addChild(root_0, ID91_tree);
                            }
                            char_literal92=(Token)match(input,54,FOLLOW_54_in_statement1067); if (state.failed) return retval;

                            }
                            break;

                    }

                    pushFollow(FOLLOW_expression_in_statement1073);
                    expression93=expression();

                    state._fsp--;
                    if (state.failed) return retval;
                    if ( state.backtracking==0 ) adaptor.addChild(root_0, expression93.getTree());
                    char_literal94=(Token)match(input,52,FOLLOW_52_in_statement1075); if (state.failed) return retval;

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
        }
        return retval;
    }
    // $ANTLR end "statement"

    public static class ids_return extends ParserRuleReturnScope {
        PseudoTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start "ids"
    // src/edu/kit/iti/algover/parser/Pseudo.g:185:1: ids : ID ( ',' ID )+ ;
    public final PseudoParser.ids_return ids() throws RecognitionException {
        PseudoParser.ids_return retval = new PseudoParser.ids_return();
        retval.start = input.LT(1);

        PseudoTree root_0 = null;

        Token ID95=null;
        Token char_literal96=null;
        Token ID97=null;

        PseudoTree ID95_tree=null;
        PseudoTree char_literal96_tree=null;
        PseudoTree ID97_tree=null;

        try {
            // src/edu/kit/iti/algover/parser/Pseudo.g:185:4: ( ID ( ',' ID )+ )
            // src/edu/kit/iti/algover/parser/Pseudo.g:186:3: ID ( ',' ID )+
            {
            root_0 = (PseudoTree)adaptor.nil();

            ID95=(Token)match(input,ID,FOLLOW_ID_in_ids1088); if (state.failed) return retval;
            if ( state.backtracking==0 ) {
            ID95_tree = (PseudoTree)adaptor.create(ID95);
            adaptor.addChild(root_0, ID95_tree);
            }
            // src/edu/kit/iti/algover/parser/Pseudo.g:186:6: ( ',' ID )+
            int cnt24=0;
            loop24:
            do {
                int alt24=2;
                int LA24_0 = input.LA(1);

                if ( (LA24_0==53) ) {
                    alt24=1;
                }


                switch (alt24) {
            	case 1 :
            	    // src/edu/kit/iti/algover/parser/Pseudo.g:186:7: ',' ID
            	    {
            	    char_literal96=(Token)match(input,53,FOLLOW_53_in_ids1091); if (state.failed) return retval;
            	    ID97=(Token)match(input,ID,FOLLOW_ID_in_ids1094); if (state.failed) return retval;
            	    if ( state.backtracking==0 ) {
            	    ID97_tree = (PseudoTree)adaptor.create(ID97);
            	    adaptor.addChild(root_0, ID97_tree);
            	    }

            	    }
            	    break;

            	default :
            	    if ( cnt24 >= 1 ) break loop24;
            	    if (state.backtracking>0) {state.failed=true; return retval;}
                        EarlyExitException eee =
                            new EarlyExitException(24, input);
                        throw eee;
                }
                cnt24++;
            } while (true);


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
        }
        return retval;
    }
    // $ANTLR end "ids"

    public static class expressions_return extends ParserRuleReturnScope {
        PseudoTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start "expressions"
    // src/edu/kit/iti/algover/parser/Pseudo.g:189:1: expressions : expression ( ',' expression )* ;
    public final PseudoParser.expressions_return expressions() throws RecognitionException {
        PseudoParser.expressions_return retval = new PseudoParser.expressions_return();
        retval.start = input.LT(1);

        PseudoTree root_0 = null;

        Token char_literal99=null;
        PseudoParser.expression_return expression98 = null;

        PseudoParser.expression_return expression100 = null;


        PseudoTree char_literal99_tree=null;

        try {
            // src/edu/kit/iti/algover/parser/Pseudo.g:189:12: ( expression ( ',' expression )* )
            // src/edu/kit/iti/algover/parser/Pseudo.g:190:3: expression ( ',' expression )*
            {
            root_0 = (PseudoTree)adaptor.nil();

            pushFollow(FOLLOW_expression_in_expressions1108);
            expression98=expression();

            state._fsp--;
            if (state.failed) return retval;
            if ( state.backtracking==0 ) adaptor.addChild(root_0, expression98.getTree());
            // src/edu/kit/iti/algover/parser/Pseudo.g:190:14: ( ',' expression )*
            loop25:
            do {
                int alt25=2;
                int LA25_0 = input.LA(1);

                if ( (LA25_0==53) ) {
                    alt25=1;
                }


                switch (alt25) {
            	case 1 :
            	    // src/edu/kit/iti/algover/parser/Pseudo.g:190:16: ',' expression
            	    {
            	    char_literal99=(Token)match(input,53,FOLLOW_53_in_expressions1112); if (state.failed) return retval;
            	    pushFollow(FOLLOW_expression_in_expressions1115);
            	    expression100=expression();

            	    state._fsp--;
            	    if (state.failed) return retval;
            	    if ( state.backtracking==0 ) adaptor.addChild(root_0, expression100.getTree());

            	    }
            	    break;

            	default :
            	    break loop25;
                }
            } while (true);


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
        }
        return retval;
    }
    // $ANTLR end "expressions"

    public static class expression_return extends ParserRuleReturnScope {
        PseudoTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start "expression"
    // src/edu/kit/iti/algover/parser/Pseudo.g:193:1: expression : or_expr ;
    public final PseudoParser.expression_return expression() throws RecognitionException {
        PseudoParser.expression_return retval = new PseudoParser.expression_return();
        retval.start = input.LT(1);

        PseudoTree root_0 = null;

        PseudoParser.or_expr_return or_expr101 = null;



        try {
            // src/edu/kit/iti/algover/parser/Pseudo.g:193:11: ( or_expr )
            // src/edu/kit/iti/algover/parser/Pseudo.g:194:3: or_expr
            {
            root_0 = (PseudoTree)adaptor.nil();

            pushFollow(FOLLOW_or_expr_in_expression1130);
            or_expr101=or_expr();

            state._fsp--;
            if (state.failed) return retval;
            if ( state.backtracking==0 ) adaptor.addChild(root_0, or_expr101.getTree());

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
        }
        return retval;
    }
    // $ANTLR end "expression"

    public static class or_expr_return extends ParserRuleReturnScope {
        PseudoTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start "or_expr"
    // src/edu/kit/iti/algover/parser/Pseudo.g:196:1: or_expr : and_expr ( ( '||' | '==>' ) or_expr )? ;
    public final PseudoParser.or_expr_return or_expr() throws RecognitionException {
        PseudoParser.or_expr_return retval = new PseudoParser.or_expr_return();
        retval.start = input.LT(1);

        PseudoTree root_0 = null;

        Token string_literal103=null;
        Token string_literal104=null;
        PseudoParser.and_expr_return and_expr102 = null;

        PseudoParser.or_expr_return or_expr105 = null;


        PseudoTree string_literal103_tree=null;
        PseudoTree string_literal104_tree=null;

        try {
            // src/edu/kit/iti/algover/parser/Pseudo.g:196:8: ( and_expr ( ( '||' | '==>' ) or_expr )? )
            // src/edu/kit/iti/algover/parser/Pseudo.g:197:3: and_expr ( ( '||' | '==>' ) or_expr )?
            {
            root_0 = (PseudoTree)adaptor.nil();

            pushFollow(FOLLOW_and_expr_in_or_expr1139);
            and_expr102=and_expr();

            state._fsp--;
            if (state.failed) return retval;
            if ( state.backtracking==0 ) adaptor.addChild(root_0, and_expr102.getTree());
            // src/edu/kit/iti/algover/parser/Pseudo.g:197:12: ( ( '||' | '==>' ) or_expr )?
            int alt27=2;
            int LA27_0 = input.LA(1);

            if ( (LA27_0==OR||LA27_0==IMPLIES) ) {
                alt27=1;
            }
            switch (alt27) {
                case 1 :
                    // src/edu/kit/iti/algover/parser/Pseudo.g:197:14: ( '||' | '==>' ) or_expr
                    {
                    // src/edu/kit/iti/algover/parser/Pseudo.g:197:14: ( '||' | '==>' )
                    int alt26=2;
                    int LA26_0 = input.LA(1);

                    if ( (LA26_0==OR) ) {
                        alt26=1;
                    }
                    else if ( (LA26_0==IMPLIES) ) {
                        alt26=2;
                    }
                    else {
                        if (state.backtracking>0) {state.failed=true; return retval;}
                        NoViableAltException nvae =
                            new NoViableAltException("", 26, 0, input);

                        throw nvae;
                    }
                    switch (alt26) {
                        case 1 :
                            // src/edu/kit/iti/algover/parser/Pseudo.g:197:15: '||'
                            {
                            string_literal103=(Token)match(input,OR,FOLLOW_OR_in_or_expr1144); if (state.failed) return retval;
                            if ( state.backtracking==0 ) {
                            string_literal103_tree = (PseudoTree)adaptor.create(string_literal103);
                            root_0 = (PseudoTree)adaptor.becomeRoot(string_literal103_tree, root_0);
                            }

                            }
                            break;
                        case 2 :
                            // src/edu/kit/iti/algover/parser/Pseudo.g:197:23: '==>'
                            {
                            string_literal104=(Token)match(input,IMPLIES,FOLLOW_IMPLIES_in_or_expr1149); if (state.failed) return retval;
                            if ( state.backtracking==0 ) {
                            string_literal104_tree = (PseudoTree)adaptor.create(string_literal104);
                            root_0 = (PseudoTree)adaptor.becomeRoot(string_literal104_tree, root_0);
                            }

                            }
                            break;

                    }

                    pushFollow(FOLLOW_or_expr_in_or_expr1153);
                    or_expr105=or_expr();

                    state._fsp--;
                    if (state.failed) return retval;
                    if ( state.backtracking==0 ) adaptor.addChild(root_0, or_expr105.getTree());

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
        }
        return retval;
    }
    // $ANTLR end "or_expr"

    public static class and_expr_return extends ParserRuleReturnScope {
        PseudoTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start "and_expr"
    // src/edu/kit/iti/algover/parser/Pseudo.g:200:1: and_expr : rel_expr ( '&&' and_expr )? ;
    public final PseudoParser.and_expr_return and_expr() throws RecognitionException {
        PseudoParser.and_expr_return retval = new PseudoParser.and_expr_return();
        retval.start = input.LT(1);

        PseudoTree root_0 = null;

        Token string_literal107=null;
        PseudoParser.rel_expr_return rel_expr106 = null;

        PseudoParser.and_expr_return and_expr108 = null;


        PseudoTree string_literal107_tree=null;

        try {
            // src/edu/kit/iti/algover/parser/Pseudo.g:200:9: ( rel_expr ( '&&' and_expr )? )
            // src/edu/kit/iti/algover/parser/Pseudo.g:201:3: rel_expr ( '&&' and_expr )?
            {
            root_0 = (PseudoTree)adaptor.nil();

            pushFollow(FOLLOW_rel_expr_in_and_expr1168);
            rel_expr106=rel_expr();

            state._fsp--;
            if (state.failed) return retval;
            if ( state.backtracking==0 ) adaptor.addChild(root_0, rel_expr106.getTree());
            // src/edu/kit/iti/algover/parser/Pseudo.g:201:12: ( '&&' and_expr )?
            int alt28=2;
            int LA28_0 = input.LA(1);

            if ( (LA28_0==AND) ) {
                alt28=1;
            }
            switch (alt28) {
                case 1 :
                    // src/edu/kit/iti/algover/parser/Pseudo.g:201:14: '&&' and_expr
                    {
                    string_literal107=(Token)match(input,AND,FOLLOW_AND_in_and_expr1172); if (state.failed) return retval;
                    if ( state.backtracking==0 ) {
                    string_literal107_tree = (PseudoTree)adaptor.create(string_literal107);
                    root_0 = (PseudoTree)adaptor.becomeRoot(string_literal107_tree, root_0);
                    }
                    pushFollow(FOLLOW_and_expr_in_and_expr1175);
                    and_expr108=and_expr();

                    state._fsp--;
                    if (state.failed) return retval;
                    if ( state.backtracking==0 ) adaptor.addChild(root_0, and_expr108.getTree());

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
        }
        return retval;
    }
    // $ANTLR end "and_expr"

    public static class rel_expr_return extends ParserRuleReturnScope {
        PseudoTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start "rel_expr"
    // src/edu/kit/iti/algover/parser/Pseudo.g:204:1: rel_expr : add_expr ( ( '<' | '>' | '==' | '<=' | '>=' ) add_expr )? ;
    public final PseudoParser.rel_expr_return rel_expr() throws RecognitionException {
        PseudoParser.rel_expr_return retval = new PseudoParser.rel_expr_return();
        retval.start = input.LT(1);

        PseudoTree root_0 = null;

        Token char_literal110=null;
        Token char_literal111=null;
        Token string_literal112=null;
        Token string_literal113=null;
        Token string_literal114=null;
        PseudoParser.add_expr_return add_expr109 = null;

        PseudoParser.add_expr_return add_expr115 = null;


        PseudoTree char_literal110_tree=null;
        PseudoTree char_literal111_tree=null;
        PseudoTree string_literal112_tree=null;
        PseudoTree string_literal113_tree=null;
        PseudoTree string_literal114_tree=null;

        try {
            // src/edu/kit/iti/algover/parser/Pseudo.g:204:9: ( add_expr ( ( '<' | '>' | '==' | '<=' | '>=' ) add_expr )? )
            // src/edu/kit/iti/algover/parser/Pseudo.g:205:3: add_expr ( ( '<' | '>' | '==' | '<=' | '>=' ) add_expr )?
            {
            root_0 = (PseudoTree)adaptor.nil();

            pushFollow(FOLLOW_add_expr_in_rel_expr1190);
            add_expr109=add_expr();

            state._fsp--;
            if (state.failed) return retval;
            if ( state.backtracking==0 ) adaptor.addChild(root_0, add_expr109.getTree());
            // src/edu/kit/iti/algover/parser/Pseudo.g:205:12: ( ( '<' | '>' | '==' | '<=' | '>=' ) add_expr )?
            int alt30=2;
            int LA30_0 = input.LA(1);

            if ( ((LA30_0>=LT && LA30_0<=EQ)) ) {
                alt30=1;
            }
            switch (alt30) {
                case 1 :
                    // src/edu/kit/iti/algover/parser/Pseudo.g:205:14: ( '<' | '>' | '==' | '<=' | '>=' ) add_expr
                    {
                    // src/edu/kit/iti/algover/parser/Pseudo.g:205:14: ( '<' | '>' | '==' | '<=' | '>=' )
                    int alt29=5;
                    switch ( input.LA(1) ) {
                    case LT:
                        {
                        alt29=1;
                        }
                        break;
                    case GT:
                        {
                        alt29=2;
                        }
                        break;
                    case EQ:
                        {
                        alt29=3;
                        }
                        break;
                    case LE:
                        {
                        alt29=4;
                        }
                        break;
                    case GE:
                        {
                        alt29=5;
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
                            // src/edu/kit/iti/algover/parser/Pseudo.g:205:15: '<'
                            {
                            char_literal110=(Token)match(input,LT,FOLLOW_LT_in_rel_expr1195); if (state.failed) return retval;
                            if ( state.backtracking==0 ) {
                            char_literal110_tree = (PseudoTree)adaptor.create(char_literal110);
                            root_0 = (PseudoTree)adaptor.becomeRoot(char_literal110_tree, root_0);
                            }

                            }
                            break;
                        case 2 :
                            // src/edu/kit/iti/algover/parser/Pseudo.g:205:22: '>'
                            {
                            char_literal111=(Token)match(input,GT,FOLLOW_GT_in_rel_expr1200); if (state.failed) return retval;
                            if ( state.backtracking==0 ) {
                            char_literal111_tree = (PseudoTree)adaptor.create(char_literal111);
                            root_0 = (PseudoTree)adaptor.becomeRoot(char_literal111_tree, root_0);
                            }

                            }
                            break;
                        case 3 :
                            // src/edu/kit/iti/algover/parser/Pseudo.g:205:29: '=='
                            {
                            string_literal112=(Token)match(input,EQ,FOLLOW_EQ_in_rel_expr1205); if (state.failed) return retval;
                            if ( state.backtracking==0 ) {
                            string_literal112_tree = (PseudoTree)adaptor.create(string_literal112);
                            root_0 = (PseudoTree)adaptor.becomeRoot(string_literal112_tree, root_0);
                            }

                            }
                            break;
                        case 4 :
                            // src/edu/kit/iti/algover/parser/Pseudo.g:205:37: '<='
                            {
                            string_literal113=(Token)match(input,LE,FOLLOW_LE_in_rel_expr1210); if (state.failed) return retval;
                            if ( state.backtracking==0 ) {
                            string_literal113_tree = (PseudoTree)adaptor.create(string_literal113);
                            root_0 = (PseudoTree)adaptor.becomeRoot(string_literal113_tree, root_0);
                            }

                            }
                            break;
                        case 5 :
                            // src/edu/kit/iti/algover/parser/Pseudo.g:205:45: '>='
                            {
                            string_literal114=(Token)match(input,GE,FOLLOW_GE_in_rel_expr1215); if (state.failed) return retval;
                            if ( state.backtracking==0 ) {
                            string_literal114_tree = (PseudoTree)adaptor.create(string_literal114);
                            root_0 = (PseudoTree)adaptor.becomeRoot(string_literal114_tree, root_0);
                            }

                            }
                            break;

                    }

                    pushFollow(FOLLOW_add_expr_in_rel_expr1219);
                    add_expr115=add_expr();

                    state._fsp--;
                    if (state.failed) return retval;
                    if ( state.backtracking==0 ) adaptor.addChild(root_0, add_expr115.getTree());

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
        }
        return retval;
    }
    // $ANTLR end "rel_expr"

    public static class add_expr_return extends ParserRuleReturnScope {
        PseudoTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start "add_expr"
    // src/edu/kit/iti/algover/parser/Pseudo.g:208:1: add_expr : mul_expr ( ( '+' | '-' | '++' ) add_expr )? ;
    public final PseudoParser.add_expr_return add_expr() throws RecognitionException {
        PseudoParser.add_expr_return retval = new PseudoParser.add_expr_return();
        retval.start = input.LT(1);

        PseudoTree root_0 = null;

        Token set117=null;
        PseudoParser.mul_expr_return mul_expr116 = null;

        PseudoParser.add_expr_return add_expr118 = null;


        PseudoTree set117_tree=null;

        try {
            // src/edu/kit/iti/algover/parser/Pseudo.g:208:9: ( mul_expr ( ( '+' | '-' | '++' ) add_expr )? )
            // src/edu/kit/iti/algover/parser/Pseudo.g:209:3: mul_expr ( ( '+' | '-' | '++' ) add_expr )?
            {
            root_0 = (PseudoTree)adaptor.nil();

            pushFollow(FOLLOW_mul_expr_in_add_expr1234);
            mul_expr116=mul_expr();

            state._fsp--;
            if (state.failed) return retval;
            if ( state.backtracking==0 ) adaptor.addChild(root_0, mul_expr116.getTree());
            // src/edu/kit/iti/algover/parser/Pseudo.g:209:12: ( ( '+' | '-' | '++' ) add_expr )?
            int alt31=2;
            int LA31_0 = input.LA(1);

            if ( ((LA31_0>=PLUS && LA31_0<=MINUS)||LA31_0==UNION) ) {
                alt31=1;
            }
            switch (alt31) {
                case 1 :
                    // src/edu/kit/iti/algover/parser/Pseudo.g:209:14: ( '+' | '-' | '++' ) add_expr
                    {
                    set117=(Token)input.LT(1);
                    set117=(Token)input.LT(1);
                    if ( (input.LA(1)>=PLUS && input.LA(1)<=MINUS)||input.LA(1)==UNION ) {
                        input.consume();
                        if ( state.backtracking==0 ) root_0 = (PseudoTree)adaptor.becomeRoot((PseudoTree)adaptor.create(set117), root_0);
                        state.errorRecovery=false;state.failed=false;
                    }
                    else {
                        if (state.backtracking>0) {state.failed=true; return retval;}
                        MismatchedSetException mse = new MismatchedSetException(null,input);
                        throw mse;
                    }

                    pushFollow(FOLLOW_add_expr_in_add_expr1251);
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
        }
        return retval;
    }
    // $ANTLR end "add_expr"

    public static class mul_expr_return extends ParserRuleReturnScope {
        PseudoTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start "mul_expr"
    // src/edu/kit/iti/algover/parser/Pseudo.g:212:1: mul_expr : prefix_expr ( ( '*' | '**' ) mul_expr )? ;
    public final PseudoParser.mul_expr_return mul_expr() throws RecognitionException {
        PseudoParser.mul_expr_return retval = new PseudoParser.mul_expr_return();
        retval.start = input.LT(1);

        PseudoTree root_0 = null;

        Token set120=null;
        PseudoParser.prefix_expr_return prefix_expr119 = null;

        PseudoParser.mul_expr_return mul_expr121 = null;


        PseudoTree set120_tree=null;

        try {
            // src/edu/kit/iti/algover/parser/Pseudo.g:212:9: ( prefix_expr ( ( '*' | '**' ) mul_expr )? )
            // src/edu/kit/iti/algover/parser/Pseudo.g:213:3: prefix_expr ( ( '*' | '**' ) mul_expr )?
            {
            root_0 = (PseudoTree)adaptor.nil();

            pushFollow(FOLLOW_prefix_expr_in_mul_expr1266);
            prefix_expr119=prefix_expr();

            state._fsp--;
            if (state.failed) return retval;
            if ( state.backtracking==0 ) adaptor.addChild(root_0, prefix_expr119.getTree());
            // src/edu/kit/iti/algover/parser/Pseudo.g:213:15: ( ( '*' | '**' ) mul_expr )?
            int alt32=2;
            int LA32_0 = input.LA(1);

            if ( (LA32_0==TIMES||LA32_0==INTERSECT) ) {
                alt32=1;
            }
            switch (alt32) {
                case 1 :
                    // src/edu/kit/iti/algover/parser/Pseudo.g:213:17: ( '*' | '**' ) mul_expr
                    {
                    set120=(Token)input.LT(1);
                    set120=(Token)input.LT(1);
                    if ( input.LA(1)==TIMES||input.LA(1)==INTERSECT ) {
                        input.consume();
                        if ( state.backtracking==0 ) root_0 = (PseudoTree)adaptor.becomeRoot((PseudoTree)adaptor.create(set120), root_0);
                        state.errorRecovery=false;state.failed=false;
                    }
                    else {
                        if (state.backtracking>0) {state.failed=true; return retval;}
                        MismatchedSetException mse = new MismatchedSetException(null,input);
                        throw mse;
                    }

                    pushFollow(FOLLOW_mul_expr_in_mul_expr1279);
                    mul_expr121=mul_expr();

                    state._fsp--;
                    if (state.failed) return retval;
                    if ( state.backtracking==0 ) adaptor.addChild(root_0, mul_expr121.getTree());

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
        }
        return retval;
    }
    // $ANTLR end "mul_expr"

    public static class prefix_expr_return extends ParserRuleReturnScope {
        PseudoTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start "prefix_expr"
    // src/edu/kit/iti/algover/parser/Pseudo.g:216:1: prefix_expr : ( '-' prefix_expr | '!' prefix_expr | postfix_expr );
    public final PseudoParser.prefix_expr_return prefix_expr() throws RecognitionException {
        PseudoParser.prefix_expr_return retval = new PseudoParser.prefix_expr_return();
        retval.start = input.LT(1);

        PseudoTree root_0 = null;

        Token char_literal122=null;
        Token char_literal124=null;
        PseudoParser.prefix_expr_return prefix_expr123 = null;

        PseudoParser.prefix_expr_return prefix_expr125 = null;

        PseudoParser.postfix_expr_return postfix_expr126 = null;


        PseudoTree char_literal122_tree=null;
        PseudoTree char_literal124_tree=null;

        try {
            // src/edu/kit/iti/algover/parser/Pseudo.g:216:12: ( '-' prefix_expr | '!' prefix_expr | postfix_expr )
            int alt33=3;
            switch ( input.LA(1) ) {
            case MINUS:
                {
                alt33=1;
                }
                break;
            case NOT:
                {
                alt33=2;
                }
                break;
            case BLOCK_BEGIN:
            case ID:
            case LIT:
            case 50:
            case 56:
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
                    // src/edu/kit/iti/algover/parser/Pseudo.g:217:5: '-' prefix_expr
                    {
                    root_0 = (PseudoTree)adaptor.nil();

                    char_literal122=(Token)match(input,MINUS,FOLLOW_MINUS_in_prefix_expr1296); if (state.failed) return retval;
                    if ( state.backtracking==0 ) {
                    char_literal122_tree = (PseudoTree)adaptor.create(char_literal122);
                    root_0 = (PseudoTree)adaptor.becomeRoot(char_literal122_tree, root_0);
                    }
                    pushFollow(FOLLOW_prefix_expr_in_prefix_expr1299);
                    prefix_expr123=prefix_expr();

                    state._fsp--;
                    if (state.failed) return retval;
                    if ( state.backtracking==0 ) adaptor.addChild(root_0, prefix_expr123.getTree());

                    }
                    break;
                case 2 :
                    // src/edu/kit/iti/algover/parser/Pseudo.g:218:5: '!' prefix_expr
                    {
                    root_0 = (PseudoTree)adaptor.nil();

                    char_literal124=(Token)match(input,NOT,FOLLOW_NOT_in_prefix_expr1305); if (state.failed) return retval;
                    if ( state.backtracking==0 ) {
                    char_literal124_tree = (PseudoTree)adaptor.create(char_literal124);
                    root_0 = (PseudoTree)adaptor.becomeRoot(char_literal124_tree, root_0);
                    }
                    pushFollow(FOLLOW_prefix_expr_in_prefix_expr1308);
                    prefix_expr125=prefix_expr();

                    state._fsp--;
                    if (state.failed) return retval;
                    if ( state.backtracking==0 ) adaptor.addChild(root_0, prefix_expr125.getTree());

                    }
                    break;
                case 3 :
                    // src/edu/kit/iti/algover/parser/Pseudo.g:219:5: postfix_expr
                    {
                    root_0 = (PseudoTree)adaptor.nil();

                    pushFollow(FOLLOW_postfix_expr_in_prefix_expr1314);
                    postfix_expr126=postfix_expr();

                    state._fsp--;
                    if (state.failed) return retval;
                    if ( state.backtracking==0 ) adaptor.addChild(root_0, postfix_expr126.getTree());

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
        }
        return retval;
    }
    // $ANTLR end "prefix_expr"

    public static class postfix_expr_return extends ParserRuleReturnScope {
        PseudoTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start "postfix_expr"
    // src/edu/kit/iti/algover/parser/Pseudo.g:222:1: postfix_expr : atom_expr ( '[' expression ']' -> ^( ARRAY_ACCESS atom_expr expression ) | -> atom_expr ) ;
    public final PseudoParser.postfix_expr_return postfix_expr() throws RecognitionException {
        PseudoParser.postfix_expr_return retval = new PseudoParser.postfix_expr_return();
        retval.start = input.LT(1);

        PseudoTree root_0 = null;

        Token char_literal128=null;
        Token char_literal130=null;
        PseudoParser.atom_expr_return atom_expr127 = null;

        PseudoParser.expression_return expression129 = null;


        PseudoTree char_literal128_tree=null;
        PseudoTree char_literal130_tree=null;
        RewriteRuleTokenStream stream_57=new RewriteRuleTokenStream(adaptor,"token 57");
        RewriteRuleTokenStream stream_56=new RewriteRuleTokenStream(adaptor,"token 56");
        RewriteRuleSubtreeStream stream_expression=new RewriteRuleSubtreeStream(adaptor,"rule expression");
        RewriteRuleSubtreeStream stream_atom_expr=new RewriteRuleSubtreeStream(adaptor,"rule atom_expr");
        try {
            // src/edu/kit/iti/algover/parser/Pseudo.g:222:13: ( atom_expr ( '[' expression ']' -> ^( ARRAY_ACCESS atom_expr expression ) | -> atom_expr ) )
            // src/edu/kit/iti/algover/parser/Pseudo.g:223:3: atom_expr ( '[' expression ']' -> ^( ARRAY_ACCESS atom_expr expression ) | -> atom_expr )
            {
            pushFollow(FOLLOW_atom_expr_in_postfix_expr1326);
            atom_expr127=atom_expr();

            state._fsp--;
            if (state.failed) return retval;
            if ( state.backtracking==0 ) stream_atom_expr.add(atom_expr127.getTree());
            // src/edu/kit/iti/algover/parser/Pseudo.g:224:3: ( '[' expression ']' -> ^( ARRAY_ACCESS atom_expr expression ) | -> atom_expr )
            int alt34=2;
            int LA34_0 = input.LA(1);

            if ( (LA34_0==56) ) {
                alt34=1;
            }
            else if ( ((LA34_0>=ENSURES && LA34_0<=DECREASES)||LA34_0==IF||LA34_0==WHILE||(LA34_0>=INVARIANT && LA34_0<=ASSERT)||(LA34_0>=OR && LA34_0<=MINUS)||(LA34_0>=TIMES && LA34_0<=BLOCK_END)||LA34_0==ID||(LA34_0>=51 && LA34_0<=53)||LA34_0==55||LA34_0==57) ) {
                alt34=2;
            }
            else {
                if (state.backtracking>0) {state.failed=true; return retval;}
                NoViableAltException nvae =
                    new NoViableAltException("", 34, 0, input);

                throw nvae;
            }
            switch (alt34) {
                case 1 :
                    // src/edu/kit/iti/algover/parser/Pseudo.g:224:5: '[' expression ']'
                    {
                    char_literal128=(Token)match(input,56,FOLLOW_56_in_postfix_expr1332); if (state.failed) return retval; 
                    if ( state.backtracking==0 ) stream_56.add(char_literal128);

                    pushFollow(FOLLOW_expression_in_postfix_expr1334);
                    expression129=expression();

                    state._fsp--;
                    if (state.failed) return retval;
                    if ( state.backtracking==0 ) stream_expression.add(expression129.getTree());
                    char_literal130=(Token)match(input,57,FOLLOW_57_in_postfix_expr1336); if (state.failed) return retval; 
                    if ( state.backtracking==0 ) stream_57.add(char_literal130);



                    // AST REWRITE
                    // elements: expression, atom_expr
                    // token labels: 
                    // rule labels: retval
                    // token list labels: 
                    // rule list labels: 
                    // wildcard labels: 
                    if ( state.backtracking==0 ) {
                    retval.tree = root_0;
                    RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.tree:null);

                    root_0 = (PseudoTree)adaptor.nil();
                    // 224:24: -> ^( ARRAY_ACCESS atom_expr expression )
                    {
                        // src/edu/kit/iti/algover/parser/Pseudo.g:224:27: ^( ARRAY_ACCESS atom_expr expression )
                        {
                        PseudoTree root_1 = (PseudoTree)adaptor.nil();
                        root_1 = (PseudoTree)adaptor.becomeRoot((PseudoTree)adaptor.create(ARRAY_ACCESS, "ARRAY_ACCESS"), root_1);

                        adaptor.addChild(root_1, stream_atom_expr.nextTree());
                        adaptor.addChild(root_1, stream_expression.nextTree());

                        adaptor.addChild(root_0, root_1);
                        }

                    }

                    retval.tree = root_0;}
                    }
                    break;
                case 2 :
                    // src/edu/kit/iti/algover/parser/Pseudo.g:225:5: 
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
                    RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.tree:null);

                    root_0 = (PseudoTree)adaptor.nil();
                    // 225:5: -> atom_expr
                    {
                        adaptor.addChild(root_0, stream_atom_expr.nextTree());

                    }

                    retval.tree = root_0;}
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
        }
        return retval;
    }
    // $ANTLR end "postfix_expr"

    public static class atom_expr_return extends ParserRuleReturnScope {
        PseudoTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start "atom_expr"
    // src/edu/kit/iti/algover/parser/Pseudo.g:228:1: atom_expr : ( ID | LIT | quantifier | '(' expression ')' | '{' ( expressions )? '}' -> ^( SETEX ( expressions )? ) | '[' ( expressions )? ']' -> ^( LISTEX ( expressions )? ) );
    public final PseudoParser.atom_expr_return atom_expr() throws RecognitionException {
        PseudoParser.atom_expr_return retval = new PseudoParser.atom_expr_return();
        retval.start = input.LT(1);

        PseudoTree root_0 = null;

        Token ID131=null;
        Token LIT132=null;
        Token char_literal134=null;
        Token char_literal136=null;
        Token char_literal137=null;
        Token char_literal139=null;
        Token char_literal140=null;
        Token char_literal142=null;
        PseudoParser.quantifier_return quantifier133 = null;

        PseudoParser.expression_return expression135 = null;

        PseudoParser.expressions_return expressions138 = null;

        PseudoParser.expressions_return expressions141 = null;


        PseudoTree ID131_tree=null;
        PseudoTree LIT132_tree=null;
        PseudoTree char_literal134_tree=null;
        PseudoTree char_literal136_tree=null;
        PseudoTree char_literal137_tree=null;
        PseudoTree char_literal139_tree=null;
        PseudoTree char_literal140_tree=null;
        PseudoTree char_literal142_tree=null;
        RewriteRuleTokenStream stream_57=new RewriteRuleTokenStream(adaptor,"token 57");
        RewriteRuleTokenStream stream_56=new RewriteRuleTokenStream(adaptor,"token 56");
        RewriteRuleTokenStream stream_BLOCK_BEGIN=new RewriteRuleTokenStream(adaptor,"token BLOCK_BEGIN");
        RewriteRuleTokenStream stream_BLOCK_END=new RewriteRuleTokenStream(adaptor,"token BLOCK_END");
        RewriteRuleSubtreeStream stream_expressions=new RewriteRuleSubtreeStream(adaptor,"rule expressions");
        try {
            // src/edu/kit/iti/algover/parser/Pseudo.g:228:10: ( ID | LIT | quantifier | '(' expression ')' | '{' ( expressions )? '}' -> ^( SETEX ( expressions )? ) | '[' ( expressions )? ']' -> ^( LISTEX ( expressions )? ) )
            int alt37=6;
            switch ( input.LA(1) ) {
            case ID:
                {
                alt37=1;
                }
                break;
            case LIT:
                {
                alt37=2;
                }
                break;
            case 50:
                {
                int LA37_3 = input.LA(2);

                if ( ((LA37_3>=MINUS && LA37_3<=NOT)||LA37_3==BLOCK_BEGIN||(LA37_3>=ID && LA37_3<=LIT)||LA37_3==50||LA37_3==56) ) {
                    alt37=4;
                }
                else if ( ((LA37_3>=ALL && LA37_3<=EX)) ) {
                    alt37=3;
                }
                else {
                    if (state.backtracking>0) {state.failed=true; return retval;}
                    NoViableAltException nvae =
                        new NoViableAltException("", 37, 3, input);

                    throw nvae;
                }
                }
                break;
            case BLOCK_BEGIN:
                {
                alt37=5;
                }
                break;
            case 56:
                {
                alt37=6;
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
                    // src/edu/kit/iti/algover/parser/Pseudo.g:229:5: ID
                    {
                    root_0 = (PseudoTree)adaptor.nil();

                    ID131=(Token)match(input,ID,FOLLOW_ID_in_atom_expr1371); if (state.failed) return retval;
                    if ( state.backtracking==0 ) {
                    ID131_tree = (PseudoTree)adaptor.create(ID131);
                    adaptor.addChild(root_0, ID131_tree);
                    }

                    }
                    break;
                case 2 :
                    // src/edu/kit/iti/algover/parser/Pseudo.g:230:5: LIT
                    {
                    root_0 = (PseudoTree)adaptor.nil();

                    LIT132=(Token)match(input,LIT,FOLLOW_LIT_in_atom_expr1377); if (state.failed) return retval;
                    if ( state.backtracking==0 ) {
                    LIT132_tree = (PseudoTree)adaptor.create(LIT132);
                    adaptor.addChild(root_0, LIT132_tree);
                    }

                    }
                    break;
                case 3 :
                    // src/edu/kit/iti/algover/parser/Pseudo.g:231:5: quantifier
                    {
                    root_0 = (PseudoTree)adaptor.nil();

                    pushFollow(FOLLOW_quantifier_in_atom_expr1383);
                    quantifier133=quantifier();

                    state._fsp--;
                    if (state.failed) return retval;
                    if ( state.backtracking==0 ) adaptor.addChild(root_0, quantifier133.getTree());

                    }
                    break;
                case 4 :
                    // src/edu/kit/iti/algover/parser/Pseudo.g:232:5: '(' expression ')'
                    {
                    root_0 = (PseudoTree)adaptor.nil();

                    char_literal134=(Token)match(input,50,FOLLOW_50_in_atom_expr1389); if (state.failed) return retval;
                    pushFollow(FOLLOW_expression_in_atom_expr1392);
                    expression135=expression();

                    state._fsp--;
                    if (state.failed) return retval;
                    if ( state.backtracking==0 ) adaptor.addChild(root_0, expression135.getTree());
                    char_literal136=(Token)match(input,51,FOLLOW_51_in_atom_expr1394); if (state.failed) return retval;

                    }
                    break;
                case 5 :
                    // src/edu/kit/iti/algover/parser/Pseudo.g:233:5: '{' ( expressions )? '}'
                    {
                    char_literal137=(Token)match(input,BLOCK_BEGIN,FOLLOW_BLOCK_BEGIN_in_atom_expr1401); if (state.failed) return retval; 
                    if ( state.backtracking==0 ) stream_BLOCK_BEGIN.add(char_literal137);

                    // src/edu/kit/iti/algover/parser/Pseudo.g:233:9: ( expressions )?
                    int alt35=2;
                    int LA35_0 = input.LA(1);

                    if ( ((LA35_0>=MINUS && LA35_0<=NOT)||LA35_0==BLOCK_BEGIN||(LA35_0>=ID && LA35_0<=LIT)||LA35_0==50||LA35_0==56) ) {
                        alt35=1;
                    }
                    switch (alt35) {
                        case 1 :
                            // src/edu/kit/iti/algover/parser/Pseudo.g:233:9: expressions
                            {
                            pushFollow(FOLLOW_expressions_in_atom_expr1403);
                            expressions138=expressions();

                            state._fsp--;
                            if (state.failed) return retval;
                            if ( state.backtracking==0 ) stream_expressions.add(expressions138.getTree());

                            }
                            break;

                    }

                    char_literal139=(Token)match(input,BLOCK_END,FOLLOW_BLOCK_END_in_atom_expr1406); if (state.failed) return retval; 
                    if ( state.backtracking==0 ) stream_BLOCK_END.add(char_literal139);



                    // AST REWRITE
                    // elements: expressions
                    // token labels: 
                    // rule labels: retval
                    // token list labels: 
                    // rule list labels: 
                    // wildcard labels: 
                    if ( state.backtracking==0 ) {
                    retval.tree = root_0;
                    RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.tree:null);

                    root_0 = (PseudoTree)adaptor.nil();
                    // 233:26: -> ^( SETEX ( expressions )? )
                    {
                        // src/edu/kit/iti/algover/parser/Pseudo.g:233:29: ^( SETEX ( expressions )? )
                        {
                        PseudoTree root_1 = (PseudoTree)adaptor.nil();
                        root_1 = (PseudoTree)adaptor.becomeRoot((PseudoTree)adaptor.create(SETEX, "SETEX"), root_1);

                        // src/edu/kit/iti/algover/parser/Pseudo.g:233:37: ( expressions )?
                        if ( stream_expressions.hasNext() ) {
                            adaptor.addChild(root_1, stream_expressions.nextTree());

                        }
                        stream_expressions.reset();

                        adaptor.addChild(root_0, root_1);
                        }

                    }

                    retval.tree = root_0;}
                    }
                    break;
                case 6 :
                    // src/edu/kit/iti/algover/parser/Pseudo.g:234:5: '[' ( expressions )? ']'
                    {
                    char_literal140=(Token)match(input,56,FOLLOW_56_in_atom_expr1421); if (state.failed) return retval; 
                    if ( state.backtracking==0 ) stream_56.add(char_literal140);

                    // src/edu/kit/iti/algover/parser/Pseudo.g:234:9: ( expressions )?
                    int alt36=2;
                    int LA36_0 = input.LA(1);

                    if ( ((LA36_0>=MINUS && LA36_0<=NOT)||LA36_0==BLOCK_BEGIN||(LA36_0>=ID && LA36_0<=LIT)||LA36_0==50||LA36_0==56) ) {
                        alt36=1;
                    }
                    switch (alt36) {
                        case 1 :
                            // src/edu/kit/iti/algover/parser/Pseudo.g:234:9: expressions
                            {
                            pushFollow(FOLLOW_expressions_in_atom_expr1423);
                            expressions141=expressions();

                            state._fsp--;
                            if (state.failed) return retval;
                            if ( state.backtracking==0 ) stream_expressions.add(expressions141.getTree());

                            }
                            break;

                    }

                    char_literal142=(Token)match(input,57,FOLLOW_57_in_atom_expr1426); if (state.failed) return retval; 
                    if ( state.backtracking==0 ) stream_57.add(char_literal142);



                    // AST REWRITE
                    // elements: expressions
                    // token labels: 
                    // rule labels: retval
                    // token list labels: 
                    // rule list labels: 
                    // wildcard labels: 
                    if ( state.backtracking==0 ) {
                    retval.tree = root_0;
                    RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.tree:null);

                    root_0 = (PseudoTree)adaptor.nil();
                    // 234:26: -> ^( LISTEX ( expressions )? )
                    {
                        // src/edu/kit/iti/algover/parser/Pseudo.g:234:29: ^( LISTEX ( expressions )? )
                        {
                        PseudoTree root_1 = (PseudoTree)adaptor.nil();
                        root_1 = (PseudoTree)adaptor.becomeRoot((PseudoTree)adaptor.create(LISTEX, "LISTEX"), root_1);

                        // src/edu/kit/iti/algover/parser/Pseudo.g:234:38: ( expressions )?
                        if ( stream_expressions.hasNext() ) {
                            adaptor.addChild(root_1, stream_expressions.nextTree());

                        }
                        stream_expressions.reset();

                        adaptor.addChild(root_0, root_1);
                        }

                    }

                    retval.tree = root_0;}
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
        }
        return retval;
    }
    // $ANTLR end "atom_expr"

    public static class quantifier_return extends ParserRuleReturnScope {
        PseudoTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start "quantifier"
    // src/edu/kit/iti/algover/parser/Pseudo.g:237:1: quantifier : '(' ( ALL | EX ) ID ':' type '::' expression ')' ;
    public final PseudoParser.quantifier_return quantifier() throws RecognitionException {
        PseudoParser.quantifier_return retval = new PseudoParser.quantifier_return();
        retval.start = input.LT(1);

        PseudoTree root_0 = null;

        Token char_literal143=null;
        Token ALL144=null;
        Token EX145=null;
        Token ID146=null;
        Token char_literal147=null;
        Token string_literal149=null;
        Token char_literal151=null;
        PseudoParser.type_return type148 = null;

        PseudoParser.expression_return expression150 = null;


        PseudoTree char_literal143_tree=null;
        PseudoTree ALL144_tree=null;
        PseudoTree EX145_tree=null;
        PseudoTree ID146_tree=null;
        PseudoTree char_literal147_tree=null;
        PseudoTree string_literal149_tree=null;
        PseudoTree char_literal151_tree=null;

        try {
            // src/edu/kit/iti/algover/parser/Pseudo.g:237:11: ( '(' ( ALL | EX ) ID ':' type '::' expression ')' )
            // src/edu/kit/iti/algover/parser/Pseudo.g:238:3: '(' ( ALL | EX ) ID ':' type '::' expression ')'
            {
            root_0 = (PseudoTree)adaptor.nil();

            char_literal143=(Token)match(input,50,FOLLOW_50_in_quantifier1447); if (state.failed) return retval;
            // src/edu/kit/iti/algover/parser/Pseudo.g:238:8: ( ALL | EX )
            int alt38=2;
            int LA38_0 = input.LA(1);

            if ( (LA38_0==ALL) ) {
                alt38=1;
            }
            else if ( (LA38_0==EX) ) {
                alt38=2;
            }
            else {
                if (state.backtracking>0) {state.failed=true; return retval;}
                NoViableAltException nvae =
                    new NoViableAltException("", 38, 0, input);

                throw nvae;
            }
            switch (alt38) {
                case 1 :
                    // src/edu/kit/iti/algover/parser/Pseudo.g:238:9: ALL
                    {
                    ALL144=(Token)match(input,ALL,FOLLOW_ALL_in_quantifier1451); if (state.failed) return retval;
                    if ( state.backtracking==0 ) {
                    ALL144_tree = (PseudoTree)adaptor.create(ALL144);
                    root_0 = (PseudoTree)adaptor.becomeRoot(ALL144_tree, root_0);
                    }

                    }
                    break;
                case 2 :
                    // src/edu/kit/iti/algover/parser/Pseudo.g:238:16: EX
                    {
                    EX145=(Token)match(input,EX,FOLLOW_EX_in_quantifier1456); if (state.failed) return retval;
                    if ( state.backtracking==0 ) {
                    EX145_tree = (PseudoTree)adaptor.create(EX145);
                    root_0 = (PseudoTree)adaptor.becomeRoot(EX145_tree, root_0);
                    }

                    }
                    break;

            }

            ID146=(Token)match(input,ID,FOLLOW_ID_in_quantifier1460); if (state.failed) return retval;
            if ( state.backtracking==0 ) {
            ID146_tree = (PseudoTree)adaptor.create(ID146);
            adaptor.addChild(root_0, ID146_tree);
            }
            char_literal147=(Token)match(input,54,FOLLOW_54_in_quantifier1462); if (state.failed) return retval;
            pushFollow(FOLLOW_type_in_quantifier1465);
            type148=type();

            state._fsp--;
            if (state.failed) return retval;
            if ( state.backtracking==0 ) adaptor.addChild(root_0, type148.getTree());
            string_literal149=(Token)match(input,DOUBLECOLON,FOLLOW_DOUBLECOLON_in_quantifier1467); if (state.failed) return retval;
            pushFollow(FOLLOW_expression_in_quantifier1470);
            expression150=expression();

            state._fsp--;
            if (state.failed) return retval;
            if ( state.backtracking==0 ) adaptor.addChild(root_0, expression150.getTree());
            char_literal151=(Token)match(input,51,FOLLOW_51_in_quantifier1472); if (state.failed) return retval;

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
        }
        return retval;
    }
    // $ANTLR end "quantifier"

    // $ANTLR start synpred1_Pseudo
    public final void synpred1_Pseudo_fragment() throws RecognitionException {   
        // src/edu/kit/iti/algover/parser/Pseudo.g:171:5: ( ID ':=' 'call' )
        // src/edu/kit/iti/algover/parser/Pseudo.g:171:6: ID ':=' 'call'
        {
        match(input,ID,FOLLOW_ID_in_synpred1_Pseudo851); if (state.failed) return ;
        match(input,ASSIGN,FOLLOW_ASSIGN_in_synpred1_Pseudo853); if (state.failed) return ;
        match(input,CALL,FOLLOW_CALL_in_synpred1_Pseudo855); if (state.failed) return ;

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


    protected DFA23 dfa23 = new DFA23(this);
    static final String DFA23_eotS =
        "\12\uffff";
    static final String DFA23_eofS =
        "\12\uffff";
    static final String DFA23_minS =
        "\1\22\1\35\4\uffff\1\26\3\uffff";
    static final String DFA23_maxS =
        "\1\67\1\65\4\uffff\1\70\3\uffff";
    static final String DFA23_acceptS =
        "\2\uffff\1\4\1\5\1\6\1\7\1\uffff\1\3\1\2\1\1";
    static final String DFA23_specialS =
        "\6\uffff\1\0\3\uffff}>";
    static final String[] DFA23_transitionS = {
            "\1\3\1\uffff\1\2\3\uffff\1\4\26\uffff\1\1\7\uffff\1\5",
            "\1\6\27\uffff\1\7",
            "",
            "",
            "",
            "",
            "\1\10\13\uffff\2\11\10\uffff\1\11\2\uffff\2\11\1\uffff\1\11"+
            "\5\uffff\1\11",
            "",
            "",
            ""
    };

    static final short[] DFA23_eot = DFA.unpackEncodedString(DFA23_eotS);
    static final short[] DFA23_eof = DFA.unpackEncodedString(DFA23_eofS);
    static final char[] DFA23_min = DFA.unpackEncodedStringToUnsignedChars(DFA23_minS);
    static final char[] DFA23_max = DFA.unpackEncodedStringToUnsignedChars(DFA23_maxS);
    static final short[] DFA23_accept = DFA.unpackEncodedString(DFA23_acceptS);
    static final short[] DFA23_special = DFA.unpackEncodedString(DFA23_specialS);
    static final short[][] DFA23_transition;

    static {
        int numStates = DFA23_transitionS.length;
        DFA23_transition = new short[numStates][];
        for (int i=0; i<numStates; i++) {
            DFA23_transition[i] = DFA.unpackEncodedString(DFA23_transitionS[i]);
        }
    }

    class DFA23 extends DFA {

        public DFA23(BaseRecognizer recognizer) {
            this.recognizer = recognizer;
            this.decisionNumber = 23;
            this.eot = DFA23_eot;
            this.eof = DFA23_eof;
            this.min = DFA23_min;
            this.max = DFA23_max;
            this.accept = DFA23_accept;
            this.special = DFA23_special;
            this.transition = DFA23_transition;
        }
        public String getDescription() {
            return "169:1: statement : ( ID ':=' expression ';' | ( ID ':=' 'call' )=>r= ID ':=' 'call' f= ID '(' ( expressions )? ')' ';' -> ^( 'call' $f ^( RESULTS $r) ^( ARGS ( expressions )? ) ) | ids ':=' 'call' ID '(' ( expressions )? ')' ';' -> ^( 'call' ID ^( RESULTS ids ) ^( ARGS ( expressions )? ) ) | 'while' expression ( invariant )+ decreases relaxedBlock | 'if' expression relaxedBlock ( options {greedy=true; } : 'else' relaxedBlock )? | 'assert' ( ID ':' )? expression ';' | 'assume' ( ID ':' )? expression ';' );";
        }
        public int specialStateTransition(int s, IntStream _input) throws NoViableAltException {
            TokenStream input = (TokenStream)_input;
        	int _s = s;
            switch ( s ) {
                    case 0 : 
                        int LA23_6 = input.LA(1);

                         
                        int index23_6 = input.index();
                        input.rewind();
                        s = -1;
                        if ( (LA23_6==CALL) && (synpred1_Pseudo())) {s = 8;}

                        else if ( ((LA23_6>=MINUS && LA23_6<=NOT)||LA23_6==BLOCK_BEGIN||(LA23_6>=ID && LA23_6<=LIT)||LA23_6==50||LA23_6==56) ) {s = 9;}

                         
                        input.seek(index23_6);
                        if ( s>=0 ) return s;
                        break;
            }
            if (state.backtracking>0) {state.failed=true; return -1;}
            NoViableAltException nvae =
                new NoViableAltException(getDescription(), 23, _s, input);
            error(nvae);
            throw nvae;
        }
    }
 

    public static final BitSet FOLLOW_method_in_program409 = new BitSet(new long[]{0x0000000000010002L});
    public static final BitSet FOLLOW_METHOD_in_method423 = new BitSet(new long[]{0x0000800000000000L});
    public static final BitSet FOLLOW_ID_in_method425 = new BitSet(new long[]{0x0004000000000000L});
    public static final BitSet FOLLOW_50_in_method427 = new BitSet(new long[]{0x0008800000000000L});
    public static final BitSet FOLLOW_vars_in_method429 = new BitSet(new long[]{0x0008000000000000L});
    public static final BitSet FOLLOW_51_in_method432 = new BitSet(new long[]{0x000010000000F000L});
    public static final BitSet FOLLOW_returns__in_method438 = new BitSet(new long[]{0x000010000000E000L});
    public static final BitSet FOLLOW_requires_in_method447 = new BitSet(new long[]{0x000010000000E000L});
    public static final BitSet FOLLOW_ensures_in_method456 = new BitSet(new long[]{0x000010000000A000L});
    public static final BitSet FOLLOW_decreases_in_method465 = new BitSet(new long[]{0x0000100000000000L});
    public static final BitSet FOLLOW_BLOCK_BEGIN_in_method472 = new BitSet(new long[]{0x0080A00001340000L});
    public static final BitSet FOLLOW_decl_in_method476 = new BitSet(new long[]{0x0080A00001340000L});
    public static final BitSet FOLLOW_statements_in_method481 = new BitSet(new long[]{0x0000200000000000L});
    public static final BitSet FOLLOW_BLOCK_END_in_method484 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_VAR_in_decl548 = new BitSet(new long[]{0x0000800000000000L});
    public static final BitSet FOLLOW_var_in_decl551 = new BitSet(new long[]{0x0010000000000000L});
    public static final BitSet FOLLOW_52_in_decl553 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_var_in_vars566 = new BitSet(new long[]{0x0020000000000002L});
    public static final BitSet FOLLOW_53_in_vars572 = new BitSet(new long[]{0x0000800000000000L});
    public static final BitSet FOLLOW_var_in_vars575 = new BitSet(new long[]{0x0020000000000002L});
    public static final BitSet FOLLOW_ID_in_var590 = new BitSet(new long[]{0x0040000000000000L});
    public static final BitSet FOLLOW_54_in_var592 = new BitSet(new long[]{0x0000400000000C00L});
    public static final BitSet FOLLOW_type_in_var594 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_INT_in_type618 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_SET_in_type622 = new BitSet(new long[]{0x0000008000000000L});
    public static final BitSet FOLLOW_LT_in_type625 = new BitSet(new long[]{0x0000000000000400L});
    public static final BitSet FOLLOW_INT_in_type628 = new BitSet(new long[]{0x0000020000000000L});
    public static final BitSet FOLLOW_GT_in_type630 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ARRAY_in_type637 = new BitSet(new long[]{0x0000008000000000L});
    public static final BitSet FOLLOW_LT_in_type640 = new BitSet(new long[]{0x0000000000000400L});
    public static final BitSet FOLLOW_INT_in_type643 = new BitSet(new long[]{0x0000020000000000L});
    public static final BitSet FOLLOW_GT_in_type645 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_RETURNS_in_returns_658 = new BitSet(new long[]{0x0004000000000000L});
    public static final BitSet FOLLOW_50_in_returns_661 = new BitSet(new long[]{0x0000800000000000L});
    public static final BitSet FOLLOW_vars_in_returns_664 = new BitSet(new long[]{0x0008000000000000L});
    public static final BitSet FOLLOW_51_in_returns_666 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_REQUIRES_in_requires679 = new BitSet(new long[]{0x0105900C00000000L});
    public static final BitSet FOLLOW_ID_in_requires683 = new BitSet(new long[]{0x0040000000000000L});
    public static final BitSet FOLLOW_54_in_requires685 = new BitSet(new long[]{0x0105900C00000000L});
    public static final BitSet FOLLOW_expression_in_requires690 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ENSURES_in_ensures702 = new BitSet(new long[]{0x0105900C00000000L});
    public static final BitSet FOLLOW_ID_in_ensures706 = new BitSet(new long[]{0x0040000000000000L});
    public static final BitSet FOLLOW_54_in_ensures708 = new BitSet(new long[]{0x0105900C00000000L});
    public static final BitSet FOLLOW_expression_in_ensures713 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_DECREASES_in_decreases725 = new BitSet(new long[]{0x0105900C00000000L});
    public static final BitSet FOLLOW_expression_in_decreases728 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_INVARIANT_in_invariant740 = new BitSet(new long[]{0x0105900C00000000L});
    public static final BitSet FOLLOW_ID_in_invariant744 = new BitSet(new long[]{0x0040000000000000L});
    public static final BitSet FOLLOW_54_in_invariant746 = new BitSet(new long[]{0x0105900C00000000L});
    public static final BitSet FOLLOW_expression_in_invariant751 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_BLOCK_BEGIN_in_block763 = new BitSet(new long[]{0x0080A00001140000L});
    public static final BitSet FOLLOW_statements_in_block765 = new BitSet(new long[]{0x0000200000000000L});
    public static final BitSet FOLLOW_BLOCK_END_in_block768 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_block_in_relaxedBlock791 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_statement_in_relaxedBlock797 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_statement_in_statements819 = new BitSet(new long[]{0x0080800001140002L});
    public static final BitSet FOLLOW_ID_in_statement836 = new BitSet(new long[]{0x0000000020000000L});
    public static final BitSet FOLLOW_ASSIGN_in_statement838 = new BitSet(new long[]{0x0105900C00000000L});
    public static final BitSet FOLLOW_expression_in_statement841 = new BitSet(new long[]{0x0010000000000000L});
    public static final BitSet FOLLOW_52_in_statement843 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ID_in_statement862 = new BitSet(new long[]{0x0000000020000000L});
    public static final BitSet FOLLOW_ASSIGN_in_statement864 = new BitSet(new long[]{0x0000000000400000L});
    public static final BitSet FOLLOW_CALL_in_statement866 = new BitSet(new long[]{0x0000800000000000L});
    public static final BitSet FOLLOW_ID_in_statement870 = new BitSet(new long[]{0x0004000000000000L});
    public static final BitSet FOLLOW_50_in_statement872 = new BitSet(new long[]{0x010D900C00000000L});
    public static final BitSet FOLLOW_expressions_in_statement874 = new BitSet(new long[]{0x0008000000000000L});
    public static final BitSet FOLLOW_51_in_statement877 = new BitSet(new long[]{0x0010000000000000L});
    public static final BitSet FOLLOW_52_in_statement879 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ids_in_statement916 = new BitSet(new long[]{0x0000000020000000L});
    public static final BitSet FOLLOW_ASSIGN_in_statement918 = new BitSet(new long[]{0x0000000000400000L});
    public static final BitSet FOLLOW_CALL_in_statement920 = new BitSet(new long[]{0x0000800000000000L});
    public static final BitSet FOLLOW_ID_in_statement922 = new BitSet(new long[]{0x0004000000000000L});
    public static final BitSet FOLLOW_50_in_statement924 = new BitSet(new long[]{0x010D900C00000000L});
    public static final BitSet FOLLOW_expressions_in_statement926 = new BitSet(new long[]{0x0008000000000000L});
    public static final BitSet FOLLOW_51_in_statement929 = new BitSet(new long[]{0x0010000000000000L});
    public static final BitSet FOLLOW_52_in_statement931 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_WHILE_in_statement966 = new BitSet(new long[]{0x0105900C00000000L});
    public static final BitSet FOLLOW_expression_in_statement969 = new BitSet(new long[]{0x0000000000800000L});
    public static final BitSet FOLLOW_invariant_in_statement977 = new BitSet(new long[]{0x0000000000808000L});
    public static final BitSet FOLLOW_decreases_in_statement986 = new BitSet(new long[]{0x0080900001140000L});
    public static final BitSet FOLLOW_relaxedBlock_in_statement994 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_IF_in_statement1000 = new BitSet(new long[]{0x0105900C00000000L});
    public static final BitSet FOLLOW_expression_in_statement1003 = new BitSet(new long[]{0x0080900001140000L});
    public static final BitSet FOLLOW_relaxedBlock_in_statement1005 = new BitSet(new long[]{0x0000000000020002L});
    public static final BitSet FOLLOW_ELSE_in_statement1026 = new BitSet(new long[]{0x0080900001140000L});
    public static final BitSet FOLLOW_relaxedBlock_in_statement1029 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ASSERT_in_statement1038 = new BitSet(new long[]{0x0105900C00000000L});
    public static final BitSet FOLLOW_ID_in_statement1043 = new BitSet(new long[]{0x0040000000000000L});
    public static final BitSet FOLLOW_54_in_statement1045 = new BitSet(new long[]{0x0105900C00000000L});
    public static final BitSet FOLLOW_expression_in_statement1051 = new BitSet(new long[]{0x0010000000000000L});
    public static final BitSet FOLLOW_52_in_statement1053 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_55_in_statement1060 = new BitSet(new long[]{0x0105900C00000000L});
    public static final BitSet FOLLOW_ID_in_statement1065 = new BitSet(new long[]{0x0040000000000000L});
    public static final BitSet FOLLOW_54_in_statement1067 = new BitSet(new long[]{0x0105900C00000000L});
    public static final BitSet FOLLOW_expression_in_statement1073 = new BitSet(new long[]{0x0010000000000000L});
    public static final BitSet FOLLOW_52_in_statement1075 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ID_in_ids1088 = new BitSet(new long[]{0x0020000000000000L});
    public static final BitSet FOLLOW_53_in_ids1091 = new BitSet(new long[]{0x0000800000000000L});
    public static final BitSet FOLLOW_ID_in_ids1094 = new BitSet(new long[]{0x0020000000000002L});
    public static final BitSet FOLLOW_expression_in_expressions1108 = new BitSet(new long[]{0x0020000000000002L});
    public static final BitSet FOLLOW_53_in_expressions1112 = new BitSet(new long[]{0x0105900C00000000L});
    public static final BitSet FOLLOW_expression_in_expressions1115 = new BitSet(new long[]{0x0020000000000002L});
    public static final BitSet FOLLOW_or_expr_in_expression1130 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_and_expr_in_or_expr1139 = new BitSet(new long[]{0x0000000140000002L});
    public static final BitSet FOLLOW_OR_in_or_expr1144 = new BitSet(new long[]{0x0105900C00000000L});
    public static final BitSet FOLLOW_IMPLIES_in_or_expr1149 = new BitSet(new long[]{0x0105900C00000000L});
    public static final BitSet FOLLOW_or_expr_in_or_expr1153 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_rel_expr_in_and_expr1168 = new BitSet(new long[]{0x0000000080000002L});
    public static final BitSet FOLLOW_AND_in_and_expr1172 = new BitSet(new long[]{0x0105900C00000000L});
    public static final BitSet FOLLOW_and_expr_in_and_expr1175 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_add_expr_in_rel_expr1190 = new BitSet(new long[]{0x00000F8000000002L});
    public static final BitSet FOLLOW_LT_in_rel_expr1195 = new BitSet(new long[]{0x0105900C00000000L});
    public static final BitSet FOLLOW_GT_in_rel_expr1200 = new BitSet(new long[]{0x0105900C00000000L});
    public static final BitSet FOLLOW_EQ_in_rel_expr1205 = new BitSet(new long[]{0x0105900C00000000L});
    public static final BitSet FOLLOW_LE_in_rel_expr1210 = new BitSet(new long[]{0x0105900C00000000L});
    public static final BitSet FOLLOW_GE_in_rel_expr1215 = new BitSet(new long[]{0x0105900C00000000L});
    public static final BitSet FOLLOW_add_expr_in_rel_expr1219 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_mul_expr_in_add_expr1234 = new BitSet(new long[]{0x0000002600000002L});
    public static final BitSet FOLLOW_set_in_add_expr1238 = new BitSet(new long[]{0x0105900C00000000L});
    public static final BitSet FOLLOW_add_expr_in_add_expr1251 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_prefix_expr_in_mul_expr1266 = new BitSet(new long[]{0x0000005000000002L});
    public static final BitSet FOLLOW_set_in_mul_expr1270 = new BitSet(new long[]{0x0105900C00000000L});
    public static final BitSet FOLLOW_mul_expr_in_mul_expr1279 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_MINUS_in_prefix_expr1296 = new BitSet(new long[]{0x0105900C00000000L});
    public static final BitSet FOLLOW_prefix_expr_in_prefix_expr1299 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_NOT_in_prefix_expr1305 = new BitSet(new long[]{0x0105900C00000000L});
    public static final BitSet FOLLOW_prefix_expr_in_prefix_expr1308 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_postfix_expr_in_prefix_expr1314 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_atom_expr_in_postfix_expr1326 = new BitSet(new long[]{0x0100000000000002L});
    public static final BitSet FOLLOW_56_in_postfix_expr1332 = new BitSet(new long[]{0x0105900C00000000L});
    public static final BitSet FOLLOW_expression_in_postfix_expr1334 = new BitSet(new long[]{0x0200000000000000L});
    public static final BitSet FOLLOW_57_in_postfix_expr1336 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ID_in_atom_expr1371 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_LIT_in_atom_expr1377 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_quantifier_in_atom_expr1383 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_50_in_atom_expr1389 = new BitSet(new long[]{0x0105900C00000000L});
    public static final BitSet FOLLOW_expression_in_atom_expr1392 = new BitSet(new long[]{0x0008000000000000L});
    public static final BitSet FOLLOW_51_in_atom_expr1394 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_BLOCK_BEGIN_in_atom_expr1401 = new BitSet(new long[]{0x0105B00C00000000L});
    public static final BitSet FOLLOW_expressions_in_atom_expr1403 = new BitSet(new long[]{0x0000200000000000L});
    public static final BitSet FOLLOW_BLOCK_END_in_atom_expr1406 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_56_in_atom_expr1421 = new BitSet(new long[]{0x0305900C00000000L});
    public static final BitSet FOLLOW_expressions_in_atom_expr1423 = new BitSet(new long[]{0x0200000000000000L});
    public static final BitSet FOLLOW_57_in_atom_expr1426 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_50_in_quantifier1447 = new BitSet(new long[]{0x000000000C000000L});
    public static final BitSet FOLLOW_ALL_in_quantifier1451 = new BitSet(new long[]{0x0000800000000000L});
    public static final BitSet FOLLOW_EX_in_quantifier1456 = new BitSet(new long[]{0x0000800000000000L});
    public static final BitSet FOLLOW_ID_in_quantifier1460 = new BitSet(new long[]{0x0040000000000000L});
    public static final BitSet FOLLOW_54_in_quantifier1462 = new BitSet(new long[]{0x0000400000000C00L});
    public static final BitSet FOLLOW_type_in_quantifier1465 = new BitSet(new long[]{0x0000000010000000L});
    public static final BitSet FOLLOW_DOUBLECOLON_in_quantifier1467 = new BitSet(new long[]{0x0105900C00000000L});
    public static final BitSet FOLLOW_expression_in_quantifier1470 = new BitSet(new long[]{0x0008000000000000L});
    public static final BitSet FOLLOW_51_in_quantifier1472 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ID_in_synpred1_Pseudo851 = new BitSet(new long[]{0x0000000020000000L});
    public static final BitSet FOLLOW_ASSIGN_in_synpred1_Pseudo853 = new BitSet(new long[]{0x0000000000400000L});
    public static final BitSet FOLLOW_CALL_in_synpred1_Pseudo855 = new BitSet(new long[]{0x0000000000000002L});

}