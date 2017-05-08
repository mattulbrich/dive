/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.theoremprover;

import edu.kit.iti.algover.ProgramDatabase;
import edu.kit.iti.algover.data.BuiltinSymbols;
import edu.kit.iti.algover.data.MapSymbolTable;
import edu.kit.iti.algover.data.SuffixSymbolTable;
import edu.kit.iti.algover.data.SymbolTable;
import edu.kit.iti.algover.parser.DafnyTree;
import edu.kit.iti.algover.symbex.AssertionElement;
import edu.kit.iti.algover.symbex.PathConditionElement;
import edu.kit.iti.algover.symbex.SymbexPath;
import edu.kit.iti.algover.symbex.VariableMap;
import edu.kit.iti.algover.term.*;
import edu.kit.iti.algover.term.builder.TermBuildException;
import edu.kit.iti.algover.util.ImmutableList;
import edu.kit.iti.algover.util.Pair;
import edu.kit.iti.algover.util.TreeUtil;

import java.util.*;

/**
 * Translation of formulas/Terms into Dafny slices
 * TODO: Var Decl auskommentieren
 * Created by sarah on 6/7/16.
 */
@Deprecated
public class DafnyTrans {

    public String methodName;
    private DafnyTree method;
    private SymbexPath path;
    private final SymbolTable symbolTable;

    public DafnyTrans(SymbexPath path) {
        this.path = path;
        this.method = path.getMethod();
        this.methodName = method.getChild(0).toString();
        this.symbolTable = makeSymbolTable();
        // TODO MU Review: Warum dieser Aufruf?
        this.trans();
    }

    /**
     * To lookup types of variables
     *
     * @return
     */
    private SymbolTable makeSymbolTable() {
        Collection<FunctionSymbol> map = new ArrayList<>();
        for (DafnyTree decl : ProgramDatabase.getAllVariableDeclarations(method)) {
            String name = decl.getChild(0).toString();
            //System.out.println(name);
            Sort sort = TreeUtil.treeToType(decl.getChild(1));
            map.add(new FunctionSymbol(name, sort));
        }

        MapSymbolTable st = new SuffixSymbolTable(new BuiltinSymbols(), map);
        return st;
    }

    /**
     * translates a formula into a DafnySlice
     * delegates to appropriate translation methods
     * @return
     */
    public String trans() {
        String assertionType ="";
        AssertionElement pob = this.path.getProofObligations().get(0);
        AssertionElement.AssertionType type = pob.getType();


        // TODO M->S: There are some new types
        switch (type) {
            case EXPLICIT_ASSERT:
                assertionType = "explicit_assertion";
                break;
            case POST:
                assertionType = "post";
                break;
            case IMPLICIT_ASSERT:
                break;
            case CALL_PRE:
                assertionType = "call_pre";
                break;
            case INVARIANT_INITIALLY_VALID:
                assertionType = "inv_init_valid";
                break;
            case INVARIANT_PRESERVED:
                assertionType = "inv_preserved";
                break;
            default:
                System.out.println("Type not supported yet");
        }
        StringBuilder method = new StringBuilder();
        StringBuilder methodDecl = createMethodDeclaration(assertionType);

        ImmutableList<PathConditionElement> pcs = path.getPathConditions();

        method.append(methodDecl+"{\n");

        Pair<String, Integer> currentSegment;
        int lineCount = 0;
        for (PathConditionElement pce : pcs) {

            currentSegment = translateAssignments(pce.getVariableMap(), lineCount);
            if (lineCount < currentSegment.getSnd()){
                lineCount = currentSegment.getSnd();
                method.append(currentSegment.getFst());
            }

            try {
                method.append("assume ("+ TreeUtil.toInfix(pce.getExpression())+");\n");
            } catch (TermBuildException e) {
                e.printStackTrace();
            }
        }
        for (AssertionElement po : path.getProofObligations()) {
            currentSegment = translateAssignments(path.getAssignmentHistory(), lineCount);
            if (lineCount < currentSegment.getSnd()){
                lineCount = currentSegment.getSnd();
                method.append(currentSegment.getFst());
            }

            try {

                method.append("assert ("+ TreeUtil.toInfix(po.getExpression())+");\n");

            } catch (TermBuildException e) {
                e.printStackTrace();
            }
        }
        method.append("}\n");
        return method.toString()+"\n";

    }



    private LinkedList<Pair<String, Sort>> getMethodArguments() {
        LinkedList<Pair<String, Sort>> arguments = new LinkedList<>();

        for (DafnyTree decl : ProgramDatabase.getArgumentDeclarations(method)) {
            String name = decl.getChild(0).toString();
            Sort sort = TreeUtil.treeToType(decl.getChild(1));
            arguments.add(new Pair<>(name, sort));
            //TODO M->S: Typing issue in the line above

        }
        return arguments;
    }

    private LinkedList<Pair<String, Sort>> getMethodReturns() {
        LinkedList<Pair<String, Sort>> arguments = new LinkedList<>();

        for (DafnyTree decl : ProgramDatabase.getReturnDeclarations(method)) {
            String name = decl.getChild(0).toString();
            Sort sort = TreeUtil.treeToType(decl.getChild(1));
            arguments.add(new Pair(name, sort));


        }
        return arguments;
    }




    private StringBuilder createMethodDeclaration(String assertionType) {
        StringBuilder sb = new StringBuilder();
        sb.append("method " + assertionType + "_" + this.methodName);

        //add the method arguments
        Pair<String, Sort> pair;
        LinkedList<Pair<String, Sort>> arguments = getMethodArguments();
        int noOfArgs = arguments.size();
        if (noOfArgs == 0) {
            sb.append("() ");
        } else {
            sb.append("(");
            Iterator<Pair<String, Sort>> pairIterator = arguments.iterator();
            while (pairIterator.hasNext()) {

                pair = pairIterator.next();
                sb.append(pair.getFst() + ": " + pair.getSnd());
                if (pairIterator.hasNext()) {
                    sb.append(", ");
                }

            }
            sb.append(") ");
        }

        //add method return arguments

        LinkedList<Pair<String, Sort>> returns = getMethodReturns();
        int noOfRet = returns.size();
        if (noOfRet == 0) {
            sb.append("");
        } else {
            sb.append("returns (");
            Iterator<Pair<String, Sort>> pairIterator = returns.iterator();
            while (pairIterator.hasNext()) {

                pair = pairIterator.next();
                sb.append(pair.getFst() + ": " + pair.getSnd());
                if (pairIterator.hasNext()) {
                    sb.append(", ");
                }

            }
            sb.append(") \n");
        }


        return sb;
    }

    /**
     * Translate variable Assignments back to Dafny
     *
     * @param vm
     */
    private Pair<String, Integer> translateAssignments(ImmutableList<DafnyTree> vm, int lastSize) {
        StringBuilder sb = new StringBuilder();
        HashMap<String, Sort> varToDecl = new HashMap<>();
        String name;
        DafnyTree expr;
        Sort s;
        int lineCount = 0;
        for (DafnyTree assignment : vm) {
            name = assignment.getChild(0).getText();
            expr = assignment.getChild(1);
            if (!varToDecl.containsKey(name)) {
                s = symbolTable.getFunctionSymbol(name).getResultSort();
                varToDecl.putIfAbsent(name, s);
            }
            try {
                if(lineCount < lastSize) { lineCount++;
                }else {
                    sb.append(name + " := " + TreeUtil.toInfix(expr) + ";\n");
                    lineCount++;
                }
            } catch (TermBuildException e) {
                e.printStackTrace();
            }

        }
        StringBuilder declarations = new StringBuilder();
        for (Map.Entry<String, Sort> e : varToDecl.entrySet()) {
            declarations.append("var " + e.getKey() + " : " + e.getValue() + ";\n");
        }
        if(lastSize != 0) {
            return new Pair<String, Integer>(sb.toString(), vm.size());
        }else{
           return new Pair<String, Integer>(declarations.toString() + sb.toString(), vm.size());
        }
    }



}
