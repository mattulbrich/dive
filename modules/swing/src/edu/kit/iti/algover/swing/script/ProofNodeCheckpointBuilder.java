package edu.kit.iti.algover.swing.script;

import edu.kit.iti.algover.nuscript.ScriptException;
import edu.kit.iti.algover.nuscript.ast.ScriptAST.Case;
import edu.kit.iti.algover.nuscript.ast.ScriptAST.Cases;
import edu.kit.iti.algover.nuscript.ast.ScriptAST.Command;
import edu.kit.iti.algover.nuscript.ast.ScriptAST.Statement;
import edu.kit.iti.algover.proof.Proof;
import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.swing.script.ProofNodeCheckpoint.Type;
import edu.kit.iti.algover.util.FunctionWithException;

import java.util.ArrayList;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;

public class ProofNodeCheckpointBuilder {
    private final Proof proof;
    private List<ProofNodeCheckpoint> checkpoints;

    public ProofNodeCheckpointBuilder(Proof proof) {
        this.proof = proof;
    }

    public void collectCheckpoints() {
        this.checkpoints = new ArrayList<>();
        collectCheckpoints(proof.getProofScript().getStatements());
    }

    private void collectCheckpoints(List<Statement> statements) {

        for (Statement statement : statements) {
            statement.visit(this::collectCommandCheckpoints,
                    this::collectCasesCheckpoints);
        }
    }

    private Void collectCasesCheckpoints(Cases cases) {
        for (Case aCase : cases.getCases()) {
            List<Statement> stms = aCase.getStatements();
            if (stms.isEmpty()) {
                checkpoints.add(ProofNodeCheckpoint.endOf(aCase, aCase.getProofNode(), Type.OPEN));
            } else {
                collectCheckpoints(stms);
            }
        }
        return null;
    }

    private Void collectCommandCheckpoints(Command command) {
        ProofNode node = command.getProofNode();
        if(node.getChildren() == null) {
            // If the execution failed, ...
            checkpoints.add(ProofNodeCheckpoint.beginOf(command, node, Type.OPEN));
            return null;
        }

        checkpoints.add(ProofNodeCheckpoint.beginOf(command, node, Type.CALL));

        if (node.getChildren().size() > 1) {
            checkpoints.add(ProofNodeCheckpoint.endOf(command, node, Type.BRANCH));
        } else {

            // since we know that this rule has been applied, we definitely know that
            // there is a continuation node recording the command!
            ProofNode continuation = node.getChildren().get(0);

            assert continuation.getCommand() == command;

            List<ProofNode> children = continuation.getChildren();

            if (children == null) {
                checkpoints.add(ProofNodeCheckpoint.endOf(command, continuation, Type.OPEN));
            } else if (children.isEmpty()) {
                checkpoints.add(ProofNodeCheckpoint.endOf(command, node, Type.CLOSED));
            }
        }

        return null;
    }

    public List<ProofNodeCheckpoint> getCheckpoints() {
        return checkpoints;
    }

    public boolean canCollect() {
        return proof.getProofScript() != null;
    }
}
