package edu.kit.iti.algover.util;

import edu.kit.iti.algover.parser.DafnyParser;
import edu.kit.iti.algover.parser.DafnyTree;
import edu.kit.iti.algover.term.Sort;
import edu.kit.iti.algover.term.builder.TermBuildException;

/**
 * Utility Class for teh translation of DafnyTrees to Strings taht represent infix repersentations
 * Created by sarah on 9/1/16.
 */
public final class TreeUtil {


    /**
     * Translate logical, integer and array access Expressions back to Dafny
     *
     * @param expr
     * @return
     * @throws TermBuildException
     */
    public static final String toInfix(DafnyTree expr) throws TermBuildException {
        StringBuilder sb = new StringBuilder();


        switch (expr.getType()) {

            case DafnyParser.ASSERT:
                return buildWithoutKeyword(expr);
            case DafnyParser.AND:
                return buildBinary("&&", expr);
            case DafnyParser.OR:
                return buildBinary("||", expr);
            case DafnyParser.IMPLIES:
                return buildBinary("==>", expr);
            case DafnyParser.GE:
                return buildBinary(">=", expr);
            case DafnyParser.GT:
                return buildBinary(">", expr);
            case DafnyParser.LE:
                return buildBinary("<=", expr);
            case DafnyParser.LT:
                return buildBinary("<", expr);
            case DafnyParser.PLUS:
                return buildBinary("+", expr);
            case DafnyParser.MINUS:
                return buildBinary("-", expr);
            case DafnyParser.TIMES:
                return buildBinary("*", expr);
       /* case DafnyParser.UNION:
            return buildBinary(BuiltinSymbols.UNION, expr);
        case DafnyParser.INTERSECT:
            return buildBinary(BuiltinSymbols.INTERSECT, expr);
        */
            case DafnyParser.NOT:
                return buildUnary("!", expr);

            case DafnyParser.EQ:
                return buildEquality(expr);

            case DafnyParser.ID:
            case DafnyParser.INT_LIT:
                return expr.toStringTree();

            case DafnyParser.LABEL:
                return buildLabel(expr);

            case DafnyParser.ALL:
                return buildQuantifier("forall", expr);
            case DafnyParser.EX:
                return buildQuantifier("exists", expr);

            case DafnyParser.LENGTH:
                return buildLength(expr);

            case DafnyParser.ARRAY_ACCESS:
                return buildArrayAccess(expr);

            case DafnyParser.ENSURES:
                return buildWithoutKeyword(expr);
            case DafnyParser.HAVOC:
                return buildHavoc(expr);

            case DafnyParser.INVARIANT:
                return buildWithoutKeyword(expr);

            default:
                TermBuildException ex = new TermBuildException("Cannot translate term: " + expr.toStringTree());
                ex.setLocation(expr);
                throw ex;
        }


    }

    /**
     * @param expr
     * @return
     */
    private static String buildHavoc(DafnyTree expr) {
        return "*";
    }

    private static String buildWithoutKeyword(DafnyTree expr) {
        String en = "";
        try {
            //System.out.println(expr.toStringTree());
            if(expr.getChildCount() == 1) {
                en = toInfix(expr.getChild(0));
            }
            if (expr.getChildCount() == 2){
                en = toInfix(expr.getChild(0)) + toInfix(expr.getChild(1));
            }
        } catch (TermBuildException e) {
            e.printStackTrace();
        }
        //System.out.println(en);
        return en;
    }

    private static String buildLabel(DafnyTree expr) {
        // ImmutableList<DafnyTree> proofObligations = path.getProofObligations();
        if (expr.getChildCount() != 1) {
            throw new RuntimeException();
        }
        String s = "";
        s = "(label : " + expr.getChild(0).toStringTree() + ") ";

        return "";
        //return s;
    }

    private static String buildArrayAccess(DafnyTree tree) throws TermBuildException {

        DafnyTree arrayTerm = tree.getChild(0);
        DafnyTree selectTerm = tree.getChild(1);
        return toInfix(arrayTerm) + "[" + toInfix(selectTerm) + "]";

    }

    private static String buildLength(DafnyTree expr) throws TermBuildException {
        return toInfix(expr.getChild(0)) + ".Length";
    }


    private static String buildEquality(DafnyTree tree) throws TermBuildException {
        if (tree.getChildCount() != 2) {
            throw new RuntimeException();
        }

        String t1 = toInfix(tree.getChild(0));
        String t2 = toInfix(tree.getChild(1));

        return "( " + t1 + " == " + t2 + " )";


    }


    private static String buildQuantifier(String q, DafnyTree tree) throws TermBuildException {
        if (tree.getChildCount() != 3) {
            throw new RuntimeException();
        }

        String var = tree.getChild(0).toString();
        System.out.println("V:" + var);
        Sort t = treeToType(tree.getChild(1));
        System.out.println(t);

        return "( " + q + " " + var + " : " + t.toString() + " :: " + toInfix(tree.getChild(2)) + " )";

    }


    private static String buildUnary(String f, DafnyTree tree) throws TermBuildException {
        if (tree.getChildCount() != 1) {
            throw new RuntimeException("Unexpected argument " + tree.toStringTree());
        }

        String t1 = toInfix(tree.getChild(0));
        return f + t1;
    }

    private static String buildBinary(String f, DafnyTree tree) throws TermBuildException {
        if (tree.getChildCount() != 2) {
            throw new RuntimeException("Unexpected argument " + tree.toStringTree());
        }

        String t1 = toInfix(tree.getChild(0));
        String t2 = toInfix(tree.getChild(1));
        return "( " + t1 + " " + f + " " + t2 + " )";
    }

    public static Sort treeToType(DafnyTree tree) {
        String name = tree.toString();
        if ("array".equals(name)) {
            name = "[int]";
        }

        return new Sort(name);
    }
}
