package edu.kit.iti.algover.proof;

import edu.kit.iti.algover.script.ScriptLanguageParser;
import edu.kit.iti.algover.script.ast.*;
import edu.kit.iti.algover.script.data.GoalNode;
import edu.kit.iti.algover.script.data.State;
import edu.kit.iti.algover.script.interpreter.Interpreter;
import edu.kit.iti.algover.script.parser.DefaultASTVisitor;
import edu.kit.iti.algover.script.parser.Facade;
import javafx.beans.property.SimpleObjectProperty;
import org.antlr.tool.Interp;
import org.antlr.v4.runtime.Token;

import java.util.ArrayList;
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
        interpreter.newState(new GoalNode<>(null, proofRoot));
        script.forEach(getInterpreter()::interpret);

        ProofNode pnext = getInterpreter().getSelectedNode().getData();
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
        public Void defaultVisit(ASTNode node) {
            lastSelectedGoalNode = interpreter.getSelectedNode();
            return null;
        }
    }

    private class ExitListener extends DefaultASTVisitor<Void> {
        @Override
        public Void defaultVisit(ASTNode node) {
            for (ProofNode children : lastSelectedGoalNode.getData().getChildren()) {
                children.setMutator(node);
            }
            return null;
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
    }
}
