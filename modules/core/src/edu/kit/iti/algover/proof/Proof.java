package edu.kit.iti.algover.proof;

import edu.kit.iti.algover.script.ScriptLanguageParser;
import edu.kit.iti.algover.script.ast.*;
import edu.kit.iti.algover.script.data.GoalNode;
import edu.kit.iti.algover.script.data.State;
import edu.kit.iti.algover.script.interpreter.Interpreter;
import edu.kit.iti.algover.script.parser.DefaultASTVisitor;
import edu.kit.iti.algover.script.parser.Facade;
import edu.kit.iti.algover.util.Util;
import javafx.beans.property.SimpleObjectProperty;
import org.antlr.tool.Interp;
import org.antlr.v4.runtime.Token;

import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedList;
import java.util.List;

/**
 * Proof Object
 * This object contains the proof root as well as teh script root
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
    private State<GoalNode<ProofNode>> currentState;

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

    public void setNewScriptTextAndParser(String script) {
        if (this.getScript() != null) {
            saveOldDataStructures();
        }
        ProofScript scriptAST = Facade.getAST(script);
        this.setScript(scriptAST.getBody());
    }
    /**
     * Parse a string representing a script and set the script to the newly parsed script AST
     *
     * @param script
     */
    public void parseAndSetScript(String script) {
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

    public Proof interpretScript() {
        assert script != null;
        assert proofRoot != null;
        lastaddedNode = proofRoot;
        interpreter.newState(new GoalNode<>(null, proofRoot));
        script.forEach(getInterpreter()::interpret);
        ProofNode pnext = getInterpreter().getSelectedNode().getData();
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

    public String proofToString() {
        StringBuilder sb = new StringBuilder("Proof for "+this.pvcName);
        sb.append(getProofRoot().toString());

        List<ProofNode> children = getProofRoot().getChildren();
            for (ProofNode child : children) {
                sb.append(child.toString());

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
 */
class ProofNodeInterpreterManager {
    final Interpreter<ProofNode> interpreter;
    private GoalNode<ProofNode> lastSelectedGoalNode;

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
            lastSelectedGoalNode.getData().setChildren(new ArrayList<>());
            interpreter.getCurrentState().getGoals().forEach(proofNodeGoalNode -> {
                lastSelectedGoalNode.getData().getChildren().add(proofNodeGoalNode.getData());
            });

            lastSelectedGoalNode.getData().addMutator(node);
            /*for (ProofNode children : lastSelectedGoalNode.getData().getChildren()) {
                children.setMutator(node);
            }*/
            return null;
        }

        @Override
        public Void visit(Statements statements) {
            return null;
        }

        @Override
        public Void visit(AssignmentStatement assignment) {
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
            return super.visit(isClosableCase);
        }

        @Override
        public Void visit(SimpleCaseStatement simpleCaseStatement) {
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
