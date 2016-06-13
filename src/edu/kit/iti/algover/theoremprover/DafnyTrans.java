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
            case POST:
                transPost();

            case IMPLICIT_ASSERT:
            case CALL_PRE:
            case INVARIANT_INITIALLY_VALID:
            case INVARIANT_PRESERVED:


        }


    }

    private LinkedList<Pair<String, Sort>> getMethodArguments(){
        LinkedList<Pair<String, Sort>> arguments = new LinkedList<>();

        for (DafnyTree decl : ProgramDatabase.getArgumentDeclarations(method)) {
            String name = decl.getChild(0).toString();
            System.out.println("ARG: "+name);
            Sort sort = treeToType(decl.getChild(1));
            System.out.println(sort);
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
    private void translatePC(DafnyTree condition){

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
        //add postcondition here?
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

        sb.append("\n}");
        System.out.println(sb);

    }

    /**
     *
     * @param vm
     */
    private String translateAssignments(VariableMap vm){
        StringBuilder sb = new StringBuilder();
       // Iterator<Pair<String, DafnyTree>> iter = vm.iterator();
        HashMap<String, Sort> varToDecl = new HashMap<>();
        String name;
        DafnyTree expr;
        Sort s;
        for (Pair<String, DafnyTree> assignment: vm) {
            name = assignment.getFst();
            expr = assignment.getSnd();
            if(!varToDecl.containsKey(name)){
               s = symbolTable.getFunctionSymbol(name).getResultSort();
                varToDecl.putIfAbsent(name,s);
            }
            sb.append(name+" := "+expr.toStringTree()+";\n");

        }
        StringBuilder declarations = new StringBuilder();
        for (Map.Entry<String, Sort> e : varToDecl.entrySet()){
            declarations.append("var "+e.getKey()+" : "+e.getValue()+";\n");
        }
        return declarations.toString()+sb.toString();

    }

    private void transPost(){
        String assertionType = "post_"+path.getPathIdentifier().toLowerCase();
        System.out.println(assertionType);

    }

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
            return buildBinary("->", expr);
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

        case DafnyParser.ALL:
            return buildQuantifier("forall", expr);
        case DafnyParser.EX:
            return buildQuantifier("exists", expr);

        case DafnyParser.LENGTH:
            return buildLength(expr);

        case DafnyParser.ARRAY_ACCESS:
            return buildArrayAccess(expr);

        default:
            TermBuildException ex = new TermBuildException("Cannot translate term: " + expr.toStringTree());
            ex.setLocation(expr);
            throw ex;
        }


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
