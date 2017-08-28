/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.theoremprover;

import edu.kit.iti.algover.ProgramDatabase;
import edu.kit.iti.algover.parser.DafnyParser;
import edu.kit.iti.algover.parser.DafnyTree;
import edu.kit.iti.algover.proof.PVC;
import edu.kit.iti.algover.symbex.AssertionElement;
import edu.kit.iti.algover.symbex.PathConditionElement;
import edu.kit.iti.algover.symbex.SymbexPath;
import edu.kit.iti.algover.term.builder.TermBuildException;
import edu.kit.iti.algover.util.ImmutableList;
import edu.kit.iti.algover.util.Pair;
import edu.kit.iti.algover.util.SymbexUtil;
import edu.kit.iti.algover.util.TreeUtil;

import java.util.*;

/**
 * Class handling the translation of a PVC to a Dafny Slice.
 * The slice does not look like original program
 * TODO keep track of line numbers and statements for backparsing of dafny result
 * New implementation of DafnyTrans
 */
public class DafnyTranslator {


    private SymbexPath path;
    private int pvcID;
    private DafnyTree method;
    private ImmutableList<DafnyTree> map;
    private String methodName;
    private String pathID;
    private AssertionElement proofObligation;
    private List<String> varsDecled;
    private int number;


    /**
     * Create a Dafny program representing the PVC given (slice of program)
     * @param verificationCondition
     * @param noOfPOs
     */
    public DafnyTranslator(PVC verificationCondition, int noOfPOs) {
        this.path = verificationCondition.getPathThroughProgram();
        this.pvcID = 0; //XXX verificationCondition.getPvcID();
        this.method = verificationCondition.getPathThroughProgram().getMethod();
        this.map = verificationCondition.getPathThroughProgram().getAssignmentHistory();
        this.methodName = this.method.getChild(0).getText();
        this.pathID = this.path.getPathIdentifier();
        this.number = noOfPOs;
        this.varsDecled = new LinkedList<>();
        System.out.println(this.trans());


    }


    public String trans() {
        ImmutableList<AssertionElement> proofObligations = this.path.getProofObligations();
        assert proofObligations.size() == 1;
        this.proofObligation = proofObligations.get(0);
        AssertionElement.AssertionType type = this.proofObligation.getType();
        String assertionType = null;
        switch (type) {
            case POST:
                assertionType = "Post";
                createPO(assertionType);
                break;
            case EXPLICIT_ASSERT:
                assertionType = "explicit_assertion";
                createPO(assertionType);
                break;
            case IMPLICIT_ASSERT:
                assertionType = "implicit_assertion";
                createPO(assertionType);
                break;
            case CALL_PRE:
                assertionType = "call_pre";
                break;
            case INVARIANT_INITIALLY_VALID:
                assertionType = "inv_init_valid";
                createPO(assertionType);
                break;
            case INVARIANT_PRESERVED:
                assertionType = "inv_preserved";
                createPO(assertionType);
                break;
            case RT_NONNULL:
                assertionType = "non_null";
                break;
            case RT_IN_BOUNDS:
                assertionType = "in_bounds";
                break;
            case VARIANT_DECREASED:
                assertionType = "loop_terminates";
                createVariantCase(assertionType);
                break;
            default:
                System.out.println("Type not supported yet");
        }
        return assertionType;
   }

    /**
     * Create the PO for showing that a loop terminates by showing that the variant is getting smaller with each loop iteration
     *
     * @param assertionType
     * @return
     */
    private StringBuilder createVariantCase(String assertionType) {
        StringBuilder method = new StringBuilder();
        method.append(createMethodDeclaration(assertionType));
        method.append("\n{\n");
        method.append(createVarDef());

        method.append(createBody(this.path.getPathConditions()));
        method.append("\n}");
        System.out.println(method.toString());
        System.out.println(SymbexUtil.toString(this.path));

        return method;
    }


    /**
     * Create String representation of Variant
     * @param temp
     * TODO check type of decreases clause and translate according to type
     * @return
     */
    private StringBuilder createVariant(Pair<String, DafnyTree> temp) throws TermBuildException {
        StringBuilder sb = new StringBuilder();
        String varName = temp.getFst();
        DafnyTree expressionAsTree = temp.getSnd();
        sb.append(varName + " := "+ TreeUtil.toInfix(temp.getSnd().getChild(0))+";\n");
        return sb;
    }

    /**
     * Create Dafny PO ensuring postcondition
     *
     * @param type
     */
    private void createPO(String type) {

        StringBuilder method = new StringBuilder();
        method.append(createMethodDeclaration(type));
        method.append("\n{\n");
        method.append(createVarDef());
        method.append(createBody(this.path.getPathConditions()));
        method.append("\n}");
        System.out.println(method.toString());
    }

    /**
     * Create an assume statement for a given pathcondition element
     *
     * @param pce
     * @return String representing the assume statement in Dafynsyntax
     * @throws TermBuildException
     */
    private String createAssumption(PathConditionElement pce) throws TermBuildException {
        String assumption = "assume ";
        assumption += TreeUtil.toInfix(pce.getExpression());
        return assumption + ";\n";
    }

    /**
     * Create VariableDeclarations of all variables in body except those that were input or output parameters
     * For keeping track a list is managed
     *
     * @return
     */
    private StringBuilder createVarDef() {
        StringBuilder sb = new StringBuilder();
        List<DafnyTree> variableDeclaration = ProgramDatabase.getAllVariableDeclarations(method);
        for (DafnyTree var : variableDeclaration) {

            if (!varsDecled.contains(var.getChild(0).getText())) {

                sb.append("var " + var.getChild(0).getText() + " : " + var.getChild(1).getText() + ";\n");
                varsDecled.add(var.getChild(0).getText());
            }
        }
        return sb;
    }

    /**
     * Creates Body of Method
     * Body is not allowed to change parameter variables.
     *
     * @param pathConditions
     * @return
     */
    private String createBody(ImmutableList<PathConditionElement> pathConditions) {
        //list of assignments, to find diff
        List<Pair<String, DafnyTree>> assignments = new LinkedList<>();
        StringBuilder body = new StringBuilder();

        try {
            for (PathConditionElement pce : pathConditions) {
                //list of assignments that will be translated
                if(pce.getType() == PathConditionElement.AssumptionType.ASSUMED_INVARIANT) {
                    String invariant = "";
                    String variant = "";
                    invariant = createAssumption(pce);

                    /*
                    LinkedList<Pair<String, DafnyTree>> assignmentsToTranslate = new LinkedList<>();
                    VariableMap variableMap = pce.getVariableMap();
                    Iterator<Pair<String, DafnyTree>> iter = variableMap.iterator();
                    Pair<String, DafnyTree> temp;
                    while (iter.hasNext()) {
                        temp = iter.next();
                        if (temp.getSnd().getType() != DafnyParser.LISTEX) {

                            //list of already printed assignments contains temp?
                            if (!assignments.contains(temp)) {
                                assignments.add(temp);
                                assignmentsToTranslate.add(temp);
                            }
                        } else {
                            variant = createVariant(temp).toString();
                            assignments.add(temp);
                        }

                    }
                    body.append(translateAssignments(reverse(assignmentsToTranslate)));
                    */
                    body.append(translateAssignments(pce.getAssignmentHistory()));
                    body.append(invariant);
                    body.append(variant);
                }


                else {

                    /*
                    LinkedList<Pair<String, DafnyTree>> assignmentsToTranslate = new LinkedList<>();
                    VariableMap variableMap = pce.getVariableMap();

                    Iterator<Pair<String, DafnyTree>> iter = variableMap.iterator();

                    Pair<String, DafnyTree> temp;

                    while (iter.hasNext()) {
                        temp = iter.next();
                        if (temp.getSnd().getType() != DafnyParser.LISTEX) {

                            if (!assignments.contains(temp)) {
                                assignments.add(temp);
                                assignmentsToTranslate.add(temp);
                            }
                        }
                    }
                    body.append(translateAssignments(reverse(assignmentsToTranslate)));
                    */
                    body.append(translateAssignments(pce.getAssignmentHistory()));
                    body.append(createAssumption(pce));
                }
            }
        } catch (TermBuildException e) {
            e.printStackTrace();
        }
        //assignments between last pce and goal
        try {
            /*
            LinkedList<Pair<String, DafnyTree>> assignmentsToTranslate = new LinkedList<>();

            Iterator<Pair<String, DafnyTree>> iter = this.map.iterator();
            Pair<String, DafnyTree> temp;
            while (iter.hasNext()) {
                temp = iter.next();
                if (temp.getSnd().getType() != DafnyParser.LISTEX) {
                    if (!assignments.contains(temp)) {

                        assignments.add(temp);
                        assignmentsToTranslate.add(temp);
                    }
                }
            }
            */
            body.append(translateAssignments(this.map));

            if(proofObligation.getType() != AssertionElement.AssertionType.VARIANT_DECREASED) {
                body.append("\nassert " + TreeUtil.toInfix(proofObligation.getExpression()) + ";");
            }else{
                body.append(translateNoetherLess(proofObligation));
            }
        } catch (TermBuildException e) {
            e.printStackTrace();
        }
        return body.toString();
    }

    /**
     * At the moment only for integer terms, translation of decreases clause to assertion:
     * show that decreases term gets strictly smaller and ist bound by zero
     * @param proofObligation
     * @return
     */
    private String translateNoetherLess(AssertionElement proofObligation) {
        DafnyTree expression = proofObligation.getExpression();
        String variableName = expression.getChild(0).toStringTree();
        DafnyTree decreasesTerm = expression.getChild(1).getChild(0);
        System.out.println(variableName + " : "+decreasesTerm.toStringTree());
        String assertion = "assert("+ "(" + variableName +" > " + decreasesTerm+") && ("+ decreasesTerm.toStringTree()  + ">= 0 ))";
        return assertion+"\n";
    }

    /**
     * Reverse input list for the right order of assignments
     * @param assignmentsToTranslate
     * @return
     */
    private List<Pair<String,DafnyTree>> reverse(LinkedList<Pair<String, DafnyTree>> assignmentsToTranslate) {
        List<Pair<String,DafnyTree>> listReversed = new LinkedList<>();
        while(assignmentsToTranslate.size() > 0){
            listReversed.add(assignmentsToTranslate.removeLast());
        }
        return listReversed;
    }

    /**
     * Translates assignments to Dafnysyntax
     *
     * @param assignmentsToTranslate list of assignments as pairs that will be translated to String representation
     * @return Dafnysyntax of assignments
     * @throws TermBuildException
     */
    private StringBuilder translateAssignments(Iterable<DafnyTree> assignmentsToTranslate) throws TermBuildException {
        StringBuilder sb = new StringBuilder();
        Iterator<DafnyTree> iter = assignmentsToTranslate.iterator();
        String assignment;

        while (iter.hasNext()) {
            DafnyTree temp = iter.next();
            assignment = TreeUtil.toInfix(temp) + ";\n";
            sb.append(assignment);
        }
        return sb;
    }

    /**
     * Creates Method declaration
     * Name consits of:
     * "method" methodname_Numberof proofbligations(if path was splitted)_PVC_correspondingPVCID_typeOfPVC(args) returns args
     * @param type
     * @return
     */
    private String createMethodDeclaration(String type) {
        //method name
        String methodDecl = " method " + this.methodName + "_" + this.number + "_PVC_" + this.pvcID + "_"+ type + "(";

        StringBuilder method = new StringBuilder();
        method.append(methodDecl);
        //create Argument list
        List<DafnyTree> argumentDeclarations = ProgramDatabase.getArgumentDeclarations(this.method);
        List<String> args = new LinkedList<>();
        for (DafnyTree arg : argumentDeclarations) {
            args.add(arg.getChild(0).getText() + ":" + arg.getChild(1).getText());
            varsDecled.add(arg.getChild(0).getText());
        }

        for (int i = 0; i < args.size(); i++) {
            method.append(args.get(i));
            if (i != args.size() - 1) {
                method.append(", ");
            }
        }

        method.append(")");

        //create return list
        List<DafnyTree> returnDeclarations = ProgramDatabase.getReturnDeclarations(this.method);
        if (returnDeclarations != null) {
            method.append(" returns (");
            List<String> rets = new LinkedList<>();
            for (DafnyTree ret : returnDeclarations) {
                rets.add(ret.getChild(0).getText() + ":" + ret.getChild(1).getText());
                varsDecled.add(ret.getChild(0).getText());
            }
            for (int i = 0; i < rets.size(); i++) {
                method.append(rets.get(i));
                if (i != rets.size() - 1) {
                    method.append(",");
                }
            }
            method.append(")");
        } else {
            method.append("\n");
        }
        return method.toString();

    }
}
