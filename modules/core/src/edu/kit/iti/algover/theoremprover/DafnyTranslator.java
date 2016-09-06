package edu.kit.iti.algover.theoremprover;

import edu.kit.iti.algover.ProgramDatabase;
import edu.kit.iti.algover.parser.DafnyTree;
import edu.kit.iti.algover.project.Assignment;
import edu.kit.iti.algover.proof.PVC;
import edu.kit.iti.algover.symbex.AssertionElement;
import edu.kit.iti.algover.symbex.PathConditionElement;
import edu.kit.iti.algover.symbex.SymbexPath;
import edu.kit.iti.algover.symbex.VariableMap;
import edu.kit.iti.algover.term.builder.TermBuildException;
import edu.kit.iti.algover.util.ImmutableList;
import edu.kit.iti.algover.util.Pair;
import edu.kit.iti.algover.util.TreeUtil;

import java.util.*;

/**
 * Class handling the translation of a PVC to a Dafny Slice. The slice does not look like original program
 * New implementation
 */
public class DafnyTranslator{



    private SymbexPath path;
    private int pvcID;
    private DafnyTree method;
    private List<Assignment> assignmentList;
    private VariableMap map;
    private String methodName;
    private String pathID;
    private AssertionElement proofObligation;
    private List<String> varsDecled;
    private int number;


    public DafnyTranslator(PVC verificationCondition, int noOfPOs){
        this.path = verificationCondition.getPathThroughProgram();
        this.pvcID = verificationCondition.getPvcID();
        this.method = verificationCondition.getPathThroughProgram().getMethod();
        this.map = verificationCondition.getPathThroughProgram().getMap();
        this.methodName = this.method.getChild(0).getText();
        this.pathID = this.path.getPathIdentifier();
        this.number = noOfPOs;
        this.varsDecled = new LinkedList<>();
        this.trans();



    }




    public String trans(){
        ImmutableList<AssertionElement> proofObligations = this.path.getProofObligations();
        assert proofObligations.size() == 1;
        this.proofObligation = proofObligations.get(0);
        AssertionElement.AssertionType type = this.proofObligation.getType();
        String assertionType = null;
        switch(type){
            case POST:
                assertionType = "Post";
                createPost(assertionType);
                break;
            case EXPLICIT_ASSERT:
                assertionType = "explicit_assertion";
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
            case  RT_NONNULL:
                break;
            case RT_IN_BOUNDS:
                break;
            case VARIANT_DECREASED:
                break;
            default:
                System.out.println("Type not supported yet");
        }

        //create Method declaration
        //create spec
        //create methodbody
        //write to stdout
        return assertionType;
    }

    /**
     * Create Dafny PO ensuring postcondition
     * @param type
     */
    private void createPost(String type) {

        StringBuilder method = new StringBuilder();
        method.append(createMethodDeclaration(type));
        method.append("\n{\n");
        method.append(createVarDef());
        method.append(createBody(this.path.getPathConditions()));
        method.append("\n}");
        System.out.println(method.toString());
    }

    /**
     * Create VariableDeclarations of all varaibles in body except those that were input or ouput parameters
     * @return
     */
    private StringBuilder createVarDef() {
        StringBuilder sb = new StringBuilder();
        List<DafnyTree> variableDeclaration = ProgramDatabase.getAllVariableDeclarations(method);
        for (DafnyTree var: variableDeclaration) {

            if(!varsDecled.contains(var.getChild(0).getText())){

                sb.append("var "+var.getChild(0).getText()+" : "+var.getChild(1).getText()+";\n");
                varsDecled.add(var.getChild(0).getText());
            }
        }

        return sb;

    }

    /**
     * Creates Body of Method
     * Body is not allowed to change parameter variables.
     * @param pathConditions
     * @return
     */
    private String createBody(ImmutableList<PathConditionElement> pathConditions) {
        List<Pair<String, DafnyTree>> assignments = new LinkedList<>();
        List<Pair<String, DafnyTree>> assignmentsToTranslate;
        StringBuilder body = new StringBuilder();
        for(PathConditionElement pce: pathConditions){
            assignmentsToTranslate = new LinkedList<>();
            if(pce.getType() == PathConditionElement.AssumptionType.PRE ||
                    pce.getType() == PathConditionElement.AssumptionType.ASSUMED_ASSERTION
                    ||pce.getType() == PathConditionElement.AssumptionType.IF_THEN){
                body.append("assume ");
            }
            if(pce.getType() == PathConditionElement.AssumptionType.IF_ELSE){
                body.append("assume ");
            }

            try {
                body.append(TreeUtil.toInfix(pce.getExpression())+";\n");


                VariableMap variableMap = pce.getVariableMap();
                Iterator<Pair<String, DafnyTree>> iter = variableMap.iterator();
                Pair<String, DafnyTree> temp;
                while(iter.hasNext()){
                    temp = iter.next();
                    if(!assignments.contains(temp)){
                        assignments.add(temp);
                        assignmentsToTranslate.add(temp);
                    }
                }
                body.append(translateAssignments(assignmentsToTranslate));

            } catch (TermBuildException e) {
                e.printStackTrace();
            }

        }

        try {
            assignmentsToTranslate = new LinkedList<>();

            Iterator<Pair<String, DafnyTree>> iter = this.map.iterator();
            Pair<String, DafnyTree> temp;
            while(iter.hasNext()){
                temp = iter.next();
                if(!assignments.contains(temp)){
                    assignments.add(temp);
                    assignmentsToTranslate.add(temp);
                }
            }
            body.append(translateAssignments(assignmentsToTranslate));


            body.append("\nassert "+TreeUtil.toInfix(proofObligation.getExpression())+";");
        } catch (TermBuildException e) {
            e.printStackTrace();
        }
        return body.toString();
    }

    /**
     * Translates assignments to Dafnysyntax
     * @param assignmentsToTranslate
     * @return
     * @throws TermBuildException
     */
    private StringBuilder translateAssignments(List<Pair<String, DafnyTree>> assignmentsToTranslate) throws TermBuildException {
        StringBuilder sb = new StringBuilder();
        Iterator<Pair<String, DafnyTree>> iter = assignmentsToTranslate.iterator();
        String assignment;
        Pair<String, DafnyTree> temp;
        while(iter.hasNext()){
            temp = iter.next();
            assignment = temp.getFst() + " := " + TreeUtil.toInfix(temp.getSnd()) + ";\n";
            sb.append(assignment);
        }
        return sb;
    }

    /**
     * Creates Method declaration
     * @param type
     * @return
     */
    private String createMethodDeclaration(String type){
        String methodDecl = " method "+this.methodName+"_"+this.number+"_"+type+"(";
        StringBuilder method = new StringBuilder();
        method.append(methodDecl);
        List<DafnyTree> argumentDeclarations = ProgramDatabase.getArgumentDeclarations(this.method);
        List<String> args = new LinkedList<>();
        for(DafnyTree arg: argumentDeclarations){
            args.add(arg.getChild(0).getText()+":"+ arg.getChild(1).getText());
            varsDecled.add(arg.getChild(0).getText());

        }
        for(int i = 0; i < args.size(); i++){
            method.append(args.get(i));
            if (i != args.size()-1){
               method.append(", ");
            }
        }
        method.append(")");

        List<DafnyTree> returnDeclarations = ProgramDatabase.getReturnDeclarations(this.method);
        if (returnDeclarations != null){
            method.append(" returns (");
            List<String> rets = new LinkedList<>();
            for(DafnyTree ret: returnDeclarations){
                rets.add(ret.getChild(0).getText()+":"+ ret.getChild(1).getText());
                 varsDecled.add(ret.getChild(0).getText());
            }
            for(int i = 0; i < rets.size(); i++) {
                method.append(rets.get(i));
                if (i != rets.size() - 1) {
                    method.append(",");
                }
            }
            method.append(")");
        }else{
            method.append("\n");
        }


        return method.toString();

    }


}
