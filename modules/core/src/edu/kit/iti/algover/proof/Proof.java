package edu.kit.iti.algover.proof;

import edu.kit.iti.algover.script.ScriptLanguageParser;
import edu.kit.iti.algover.script.ast.*;
//import edu.kit.iti.algover.script.data.GoalNode;
import edu.kit.iti.algover.script.data.State;
import edu.kit.iti.algover.script.interpreter.Interpreter;
import edu.kit.iti.algover.script.parser.DefaultASTVisitor;
import edu.kit.iti.algover.script.parser.Facade;
import edu.kit.iti.algover.util.ProofTreeUtil;
import edu.kit.iti.algover.util.Util;
import javafx.beans.property.SimpleObjectProperty;
import org.antlr.tool.Interp;
import org.antlr.v4.runtime.Token;

import java.util.*;

/**
 * Proof Object
 * This object contains the proof root as well as the script root
 * It has to be build by the ProjectManager in order to contain a valid interpreter.
 */
public class Proof {


    /**
     * Status of Proof
     */

    private SimpleObjectProperty<ProofStatus> proofStatus = new SimpleObjectProperty<>(null, "ProofStatusProperty");
    /**
     * Root of logical Proof
     */
    private ProofNode proofRoot;

    private ProofNode lastaddedNode;

    /**
     * Root of Script
     */
    private Statements script;

    /**
     * PVC Name for which this proof object is created
     */
    private String pvcName;

    /**
     * Current state from interpreter
     */
    private State<ProofNode> currentState;

    /**
     * Interpreter for this proof
     */
    private Interpreter<ProofNode> interpreter;


    public Proof(String pvcName) {
        this.setPvcName(pvcName);
        this.setProofRoot(null);
        this.setProofStatus(ProofStatus.NOT_LOADED);
        this.script = new Statements();

    }

    /**
     * Parses a script as string representation and sets the parsed AST
     *
     * @param script string representation of script
     */
    public void setNewScriptTextAndParser(String script) {
        if (this.getScript() != null) {
            saveOldDataStructures();
        }
        if (script.equals("")) {
            ProofScript scriptAST = Facade.getAST("script empty (){}");
            this.setScript(scriptAST.getBody());
        } else {
            ProofScript scriptAST = Facade.getAST(script);
            this.setScript(scriptAST.getBody());
        }
    }

    /**
     * Parse a script in a script file  and set the script to the newly parsed script AST
     *
     * @param script
     */
    public void parseScriptFileAndSetScript(String script) {
        if (this.getScript() != null) {
            saveOldDataStructures();
        }

        ProofScript scriptAST = Facade.getAST(Util.maskFileName(script));
        this.setScript(scriptAST.getBody());

    }

    /**
     * Save the old script and the old proof for comparison when reloading
     */
    private void saveOldDataStructures() {
    }


    public ProofNode getProofRoot() {
        return proofRoot;
    }

    public void setProofRoot(ProofNode proofRoot) {
        this.proofRoot = proofRoot;
    }

    public String getPvcName() {
        return pvcName;
    }

    public void setPvcName(String pvcName) {
        this.pvcName = pvcName;
    }

    public SimpleObjectProperty<ProofStatus> proofStatusProperty() {
        return proofStatus;
    }

    public Interpreter<ProofNode> getInterpreter() {
        return interpreter;
    }

    public void setInterpreter(Interpreter<ProofNode> interpreter) {
        this.interpreter = interpreter;
        new ProofNodeInterpreterManager(interpreter);
    }


    /**
     * Replay proof
     *
     * @return
     */
    public Proof replay() {
        if (getProofRoot() != null | getScript() != null) {
            saveOldDataStructures();
        }
        if (getProofStatus().equals(ProofStatus.DIRTY)) {
            //reload
            //
            setProofStatus(ProofStatus.OPEN);
        } else {
            setProofStatus(ProofStatus.NON_EXISTING);
        }
        return this;
    }

    /**
     * Interpret Script. For this the interpretr, the script ast and teh proof root have to be set.
     *
     * @return
     */
    public Proof interpretScript() {
        assert script != null;
        assert proofRoot != null;
        assert interpreter != null;
        lastaddedNode = proofRoot;
        interpreter.newState(proofRoot);
        script.forEach(getInterpreter()::interpret);
        ProofNode pnext = getInterpreter().getSelectedNode();
        // System.out.println("pnext.getSequent() = " + pnext.getSequent());
        return this;
    }

    /**
     * Interpret next String representation of possible ASTNode and update the ASTNode as well as the ProofNode
     *
     * @param script
     */
    public void interpretASTNode(String script) {
        if (this.script != null && !this.script.isEmpty()) {
            int i = this.script.size();
            Statement lastStatement = this.script.get(i - 1);
            Token lastToken = lastStatement.getRuleContext().getStop();
            script = script.substring(lastToken.getStopIndex());
        }
        ProofScript newAst = Facade.getAST(script);
        newAst.getBody().forEach(s -> {
            System.out.println("Interpreting s = " + s);
            getInterpreter().interpret(s);
            this.script.add(s);
        });

    }

    /**
     * Set a new Script , parse it and interpret script.
     *
     * @param scriptText
     * @return this object
     */
    public Proof setNewScriptTextAndInterpret(String scriptText) {
        if (interpreter == null) {
            throw new RuntimeException("No interpreter is set");
        } else {
            this.setNewScriptTextAndParser(scriptText);
            this.interpretScript();
            return this;
        }
    }

    public ProofStatus getProofStatus() {
        return proofStatus.get();
    }

    public void setProofStatus(ProofStatus proofStatus) {
        this.proofStatus.set(proofStatus);
    }


    public Statements getScript() {
        return script;
    }

    public void setScript(Statements script) {
        this.script = script;
    }


    /**
     * Returns a string representation of the proof tree
     *
     * @return
     */
    public String proofToString() {
        StringBuilder sb = new StringBuilder("Proof for " + this.pvcName + "\n");
        if (this.getProofRoot() != null) {
            sb.append(ProofTreeUtil.toStringTree(getProofRoot()));
        }
        return sb.toString();
    }

    /**
     * This method invalidates this proof object, sets the status to dirty
     */
    public void invalidate() {
        this.setProofStatus(ProofStatus.DIRTY);

    }
}

/**
 * Class handling the creation of the proof tree when interpreting script.
 * EntryListeners are informed when entering an ASTNode in the Interpreter
 * ExitsListeners are informed at then end of ASTNodes
 */
class ProofNodeInterpreterManager {
    final Interpreter<ProofNode> interpreter;
    private ProofNode lastSelectedGoalNode;

    public ProofNodeInterpreterManager(Interpreter<ProofNode> interpreter) {
        this.interpreter = interpreter;
        interpreter.getExitListeners().add(new ExitListener());
        interpreter.getEntryListeners().add(new EntryListener());
    }


    private class EntryListener extends DefaultASTVisitor<Void> {
        @Override
        public Void visit(Statements statements) {
            return null;
        }

        @Override
        public Void defaultVisit(ASTNode node) {
            lastSelectedGoalNode = interpreter.getSelectedNode();
            return null;
        }

        @Override
        public Void visit(AssignmentStatement assignment) {
            return defaultVisit(assignment);
            /*if(lastSelectedGoalNode == null )
                return defaultVisit(assignment);
            return null;*/
        }

        @Override
        public Void visit(SimpleCaseStatement simpleCaseStatement) {
            return null;
        }

        @Override
        public Void visit(MatchExpression matchExpression) {
            return null;
        }

        @Override
        public Void visit(Signature signature) {
            return null;
        }

        @Override
        public Void visit(Parameters parameters) {
            return null;
        }

        @Override
        public Void visit(IntegerLiteral integer) {
            return null;
        }

        @Override
        public Void visit(BinaryExpression binaryExpression) {
            return null;
        }

        @Override
        public Void visit(TermLiteral termLiteral) {
            return null;
        }

        @Override
        public Void visit(SequentLiteral sequentLiteral) {
            return null;
        }

        @Override
        public Void visit(StringLiteral stringLiteral) {
            return null;
        }

        @Override
        public Void visit(Variable variable) {
            return null;
        }

        @Override
        public Void visit(BooleanLiteral booleanLiteral) {
            return null;
        }
    }

    private class ExitListener extends DefaultASTVisitor<Void> {
        @Override
        public Void visit(SimpleCaseStatement simpleCaseStatement) {
            return null;
        }


        @Override
        public Void visit(MatchExpression matchExpression) {
            return null;
        }

        @Override
        public Void visit(Signature signature) {
            return null;
        }

        @Override
        public Void visit(Parameters parameters) {
            return null;
        }

        @Override
        public Void defaultVisit(ASTNode node) {

            lastSelectedGoalNode.setChildren(new ArrayList<>());

            List<ProofNode> goals = interpreter.getCurrentState().getGoals();

            if (goals.size() == 1 && goals.get(0).equals(lastSelectedGoalNode)) {
                System.out.println("There was no change");
                return null;
            }
            if (goals.size() > 0) {
                for (ProofNode goal : goals) {
                    lastSelectedGoalNode.getChildren().add(goal);

                }
            }

            lastSelectedGoalNode.addMutator(node);
            return null;
        }

        @Override
        public Void visit(Statements statements) {
            return null;
        }


        /**
         * When exiting an Assignment statement a new node has to be added, because assignments change the state as well
         *
         * @param assignment
         * @return
         */
        @Override
        public Void visit(AssignmentStatement assignment) {
         /*   LinkedList<ProofNode> singleChild = new LinkedList<>();
            List<ProofNode> goals = interpreter.getCurrentState().getGoals();


            if (goals.size() == 1) {
                //singleChild.add(goals.get(0).getData());
                ProofNode pn = new ProofNode(lastSelectedGoalNode,
                        null,
                        lastSelectedGoalNode.getHistory(),
                        goals.get(0).getSequent(), lastSelectedGoalNode.getRootPVC());
                pn.setVariableAssignments(lastSelectedGoalNode.getVariableAssignments().deepCopy());

                goals.get(0).addMutator(assignment);
                singleChild.add(goals.get(0));
            }
            lastSelectedGoalNode.setChildren(singleChild);
            //lastSelectedGoalNode.addMutator(assignment);
            return null;*/
            return defaultVisit(assignment);
        }

        @Override
        public Void visit(CasesStatement casesStatement) {

            return null;
        }

        @Override
        public Void visit(CaseStatement caseStatement) {
            return null;
        }

        @Override
        public Void visit(IsClosableCase isClosableCase) {
            return null;
        }



        @Override
        public Void visit(IntegerLiteral integer) {
            return null;
        }

        @Override
        public Void visit(BinaryExpression binaryExpression) {
            return null;
        }

        @Override
        public Void visit(TermLiteral termLiteral) {
            return null;
        }

        @Override
        public Void visit(SequentLiteral sequentLiteral) {
            return null;
        }

        @Override
        public Void visit(StringLiteral stringLiteral) {
            return null;
        }

        @Override
        public Void visit(Variable variable) {
            return null;
        }

        @Override
        public Void visit(BooleanLiteral booleanLiteral) {
            return null;
        }
    }
}
