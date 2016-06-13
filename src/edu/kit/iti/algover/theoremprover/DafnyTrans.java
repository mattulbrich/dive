package edu.kit.iti.algover.theoremprover;

import edu.kit.iti.algover.ProgramDatabase;
import edu.kit.iti.algover.data.BuiltinSymbols;
import edu.kit.iti.algover.data.MapSymbolTable;
import edu.kit.iti.algover.data.SuffixSymbolTable;
import edu.kit.iti.algover.data.SymbolTable;
import edu.kit.iti.algover.parser.DafnyParser;
import edu.kit.iti.algover.parser.DafnyTree;
import edu.kit.iti.algover.symbex.PathConditionElement;
import edu.kit.iti.algover.symbex.SymbexPath;
import edu.kit.iti.algover.symbex.VariableMap;
import edu.kit.iti.algover.term.*;
import edu.kit.iti.algover.term.builder.TermBuildException;
import edu.kit.iti.algover.util.ImmutableList;
import edu.kit.iti.algover.util.Pair;

import java.util.*;

/**
 * Translation of formulas/Terms into Dafny slices
 * Created by sarah on 6/7/16.
 */
public class DafnyTrans {

    private String methodName;
    private DafnyTree method;
    //public String assertionType;
    private SymbexPath path;
    private final SymbolTable symbolTable;

    public DafnyTrans(SymbexPath path){
        this.path = path;
        this.method = path.getMethod();
        this.methodName = method.getChild(0).toString();
        this.symbolTable = makeSymbolTable();
        this.trans();
    }

    /**
     * ATM:_ Don't know whether I need it
     * @return
     */
    private SymbolTable makeSymbolTable() {
        Collection<FunctionSymbol> map = new ArrayList<>();
        for (DafnyTree decl : ProgramDatabase.getAllVariableDeclarations(method)) {
            String name = decl.getChild(0).toString();
            System.out.println(name);
            Sort sort = treeToType(decl.getChild(1));
            map.add(new FunctionSymbol(name, sort));
        }

        MapSymbolTable st = new SuffixSymbolTable(new BuiltinSymbols(), map);
        return st;
    }

    /** translates a formula into a DafnySlice
     *
     * @return
     */
    public void trans(){

        switch(this.path.getProofObligationType()){
            case EXPLICIT_ASSERT:
                transExplicitAssert();
                break;
            case POST:
                transPost();
                break;
            case IMPLICIT_ASSERT:
                break;
            case CALL_PRE:
                break;

            case INVARIANT_INITIALLY_VALID:
                transInvInit();
                break;
            case INVARIANT_PRESERVED:
                break;


        }


    }

    private String transInvInit() {
        String assertionType = "inv_init_valid";
        ImmutableList<PathConditionElement> pcs =  path.getPathConditions();

        StringBuilder methodDecl = createMethodDeclaration(assertionType);
        StringBuilder spec = new StringBuilder();
        for (PathConditionElement pce: pcs) {
            if(pce.getType().equals(PathConditionElement.AssumptionType.PRE)) {
                spec.append(createPrecondition(pce));
            }
        }

        StringBuilder block = new StringBuilder();


        //Block Begin
        block.append("\n{\n");
        String assertStmt;
        for (DafnyTree po: path.getProofObligations()) {
            try {

                assertStmt = translateInv(po);
                block.append(translateAssignments(path.getMap()));
                block.append("assert "+assertStmt+";");
                System.out.println(assertStmt);
            }
            catch (TermBuildException e) {
                e.printStackTrace();
            }
        }
//
//        //Block End
//        block.append("\n}");
//
        methodDecl.append(spec).append(block);
        System.out.println(methodDecl.toString());

        return methodDecl.toString();


    }

    private String translateInv(DafnyTree po) throws TermBuildException {
        StringBuilder invFormula = new StringBuilder();
        List<DafnyTree> children = po.getChildren();
        for (DafnyTree form: children) {
            invFormula.append(toInfix(form));
        }
        System.out.println(invFormula.toString());
        return invFormula.toString();
    }

    private LinkedList<Pair<String, Sort>> getMethodArguments(){
        LinkedList<Pair<String, Sort>> arguments = new LinkedList<>();

        for (DafnyTree decl : ProgramDatabase.getArgumentDeclarations(method)) {
            String name = decl.getChild(0).toString();
            Sort sort = treeToType(decl.getChild(1));
            arguments.add(new Pair(name, sort));


        }
        return arguments;
    }

    private LinkedList<Pair<String, Sort>> getMethodReturns(){
        LinkedList<Pair<String, Sort>> arguments = new LinkedList<>();

        for (DafnyTree decl : ProgramDatabase.getReturnDeclarations(method)) {
            String name = decl.getChild(0).toString();
            Sort sort = treeToType(decl.getChild(1));
            arguments.add(new Pair(name, sort));


        }
        return arguments;
    }

    private static Sort treeToType(DafnyTree tree) {
        String name = tree.toString();
        if("array".equals(name)) {
            name = "seq<int>";
        }

        return new Sort(name);
    }




    private StringBuilder createMethodDeclaration(String assertionType){
        StringBuilder sb = new StringBuilder();
        sb.append("method "+assertionType+"_"+this.methodName);

       //add the method arguments
        Pair<String, Sort> pair;
        LinkedList<Pair<String, Sort>> arguments = getMethodArguments();
        int noOfArgs = arguments.size();
        if(noOfArgs == 0){
            sb.append("() ");
        }else{
            sb.append("(");
            Iterator<Pair<String,Sort>> pairIterator = arguments.iterator();
            while(pairIterator.hasNext()) {

                pair = pairIterator.next();
                sb.append(pair.getFst()+": "+pair.getSnd());
                if(pairIterator.hasNext()){
                    sb.append(", ");
                }

            }
            sb.append(") ");
        }

        //add method return arguments

        LinkedList<Pair<String, Sort>> returns = getMethodReturns();
        int noOfRet = returns.size();
        if(noOfRet == 0){
            sb.append("");
        }else{
            sb.append("returns (");
            Iterator<Pair<String,Sort>> pairIterator = returns.iterator();
            while(pairIterator.hasNext()) {

                pair = pairIterator.next();
                sb.append(pair.getFst()+": "+pair.getSnd());
                if(pairIterator.hasNext()){
                    sb.append(", ");
                }

            }
            sb.append(") \n");
        }


        return sb;
    }


    private String createPrecondition(PathConditionElement precondition){
        StringBuilder sb = new StringBuilder();
        sb.append("requires ");


        try {
            sb.append(toInfix(precondition.getExpression())+"\n");
        } catch (TermBuildException e) {
            e.printStackTrace();
        }

        return sb.toString();
    }

    private String transPost(){
        String assertionType = "post";
        ImmutableList<PathConditionElement> pcs =  path.getPathConditions();

        StringBuilder methodDecl = createMethodDeclaration(assertionType);
        StringBuilder spec = new StringBuilder();
        for (PathConditionElement pce: pcs) {
            if(pce.getType().equals(PathConditionElement.AssumptionType.PRE)) {
                spec.append(createPrecondition(pce));
            }
        }
        StringBuilder block = new StringBuilder();


        //Block Begin
        block.append("\n{\n");
        String assertStmt;
        for (DafnyTree po: path.getProofObligations()) {

            try {
                        assertStmt = toInfix(po);
                        block.append(translateAssignments(path.getMap()));
                        spec.append(assertStmt);
            }

            catch (TermBuildException e) {
                e.printStackTrace();
            }
        }

        //Block End
        block.append("\n}");

        methodDecl.append(spec).append(block);
        System.out.println(methodDecl.toString());

        return methodDecl.toString();


    }



    /**
     * translates explicit assertions to Dafny
     */
    private void transExplicitAssert(){
        String assertionType = "explicit_assert";
        ImmutableList<PathConditionElement> pcs =  path.getPathConditions();

        StringBuilder sb = createMethodDeclaration(assertionType);

        for (PathConditionElement pce: pcs) {
            if(pce.getType().equals(PathConditionElement.AssumptionType.PRE)) {
                sb.append(createPrecondition(pce));
            }

        }


        //Block Begin
        sb.append("\n{\n");
        String assertStmt;
        for (DafnyTree po: path.getProofObligations()) {
            try {

                assertStmt =  toInfix(po);
                sb.append(translateAssignments(path.getMap()));
                sb.append(assertStmt);}

            catch (TermBuildException e) {
                e.printStackTrace();
            }
        }

        //Block End
        sb.append("\n}");
        System.out.println(sb);

    }

    /**
     * Translate variable Assignments back to Dafny
     * @param vm
     */
    private String translateAssignments(VariableMap vm){
        StringBuilder sb = new StringBuilder();
        HashMap<String, Sort> varToDecl = new HashMap<>();
        String name;
        DafnyTree expr;
        Sort s;
        List<Pair<String, DafnyTree>> list = vm.toList();
        Collections.reverse(list);
        for (Pair<String, DafnyTree> assignment: list) {
            name = assignment.getFst();
            expr = assignment.getSnd();
            if(!varToDecl.containsKey(name)){
               s = symbolTable.getFunctionSymbol(name).getResultSort();
                varToDecl.putIfAbsent(name,s);
            }
            try {
                sb.append(name+" := "+ toInfix(expr)+";\n");
            } catch (TermBuildException e) {
                e.printStackTrace();
            }

        }
        StringBuilder declarations = new StringBuilder();
        for (Map.Entry<String, Sort> e : varToDecl.entrySet()){
            declarations.append("var "+e.getKey()+" : "+e.getValue()+";\n");
        }
        return declarations.toString()+sb.toString();

    }


    /**
     * Translate logical, integer and array access Expressions back to Dafny
     * @param expr
     * @return
     * @throws TermBuildException
     */
    private String toInfix(DafnyTree expr) throws TermBuildException{
        StringBuilder sb = new StringBuilder();


        switch(expr.getType()) {

        case DafnyParser.ASSERT:
            return buildUnary("assert", expr);
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
        case DafnyParser.LIT:
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
            return buildEnsures(expr);
        case DafnyParser.HAVOC:
            return buildHavoc(expr);

        default:
            TermBuildException ex = new TermBuildException("Cannot translate term: " + expr.toStringTree());
            ex.setLocation(expr);
            throw ex;
        }


    }

    /**
     * todo build Havoc expr
     * @param expr
     * @return
     */
    private String buildHavoc(DafnyTree expr) {
        return expr.toStringTree();
    }

    private String buildEnsures(DafnyTree expr){
        String en ="";
        try {
            en = "ensures "+ toInfix(expr.getChild(0)) + toInfix(expr.getChild(1));
        } catch (TermBuildException e) {
            e.printStackTrace();
        }
        System.out.println(en);
        return en;
    }
    private String buildLabel(DafnyTree expr) {
       // ImmutableList<DafnyTree> proofObligations = path.getProofObligations();
         if(expr.getChildCount() != 1) {
            throw new RuntimeException();
        }
        String s = "";
        s = "(label : "+ expr.getChild(0).toStringTree() +") ";
        return s;
    }

    private String buildArrayAccess(DafnyTree tree) throws TermBuildException {

        DafnyTree arrayTerm = tree.getChild(0);
        DafnyTree selectTerm = tree.getChild(1);
        return toInfix(arrayTerm)+"["+toInfix(selectTerm) +"]";

    }

    private String buildLength(DafnyTree expr) throws TermBuildException {
        return toInfix(expr.getChild(0))+".Length";
    }


    private String buildEquality(DafnyTree tree) throws TermBuildException {
        if(tree.getChildCount() != 2) {
            throw new RuntimeException();
        }

        String t1 = toInfix(tree.getChild(0));
        String t2 = toInfix(tree.getChild(1));

        return "( "+ t1 + " == " + t2 + " )";


    }


    private String buildQuantifier(String q, DafnyTree tree) throws TermBuildException {
        if(tree.getChildCount() != 3) {
            throw new RuntimeException();
        }

        String var = tree.getChild(0).toString();
        System.out.println("V:"+var);
        Sort t = treeToType(tree.getChild(1));
        System.out.println(t);

        return "( "+q+" "+var+" : "+ t.toString() +" :: " +toInfix(tree.getChild(2)) +" )";

    }


    private String buildUnary(String f, DafnyTree tree) throws TermBuildException {
        if(tree.getChildCount() != 1) {
            throw new RuntimeException("Unexpected argument " + tree.toStringTree());
        }

        String t1 = toInfix(tree.getChild(0));
        return  f + t1;
    }

    private String buildBinary(String f, DafnyTree tree) throws TermBuildException {
        if(tree.getChildCount() != 2) {
            throw new RuntimeException("Unexpected argument " + tree.toStringTree());
        }

        String t1 = toInfix(tree.getChild(0));
        String t2 = toInfix(tree.getChild(1));
        return "( "+ t1+ " " + f+ " " + t2+ " )";
    }
}
