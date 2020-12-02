package edu.kit.iti.algover.rule.script;

import edu.kit.iti.algover.nuscript.ScriptAST;
import edu.kit.iti.algover.nuscript.ScriptAST.*;
import edu.kit.iti.algover.proof.Proof;
import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.rule.script.ProofNodeCheckpoint.Type;
import org.antlr.v4.runtime.Token;

import java.util.ArrayList;
import java.util.List;

public class ProofNodeCheckpointBuilder {
    private final Proof proof;
    private List<ProofNodeCheckpoint> checkpoints;

    public ProofNodeCheckpointBuilder(Proof proof) {
        this.proof = proof;
    }

    public void collectCheckpoints() {
        this.checkpoints = new ArrayList<>();
        collectCheckpoints(proof.getProofScript());
    }

    private void collectCheckpoints(Script script) {
        for (Statement statement : script.getStatements()) {
            statement.visit((cmd) ->  collectCommandCheckpoints(script, cmd),
                    (cases) -> collectCasesCheckpoints(script, cases));
        }
    }

    private void collectCheckpoints(Case caze) {
        for (Statement statement : caze.getStatements()) {
            statement.visit((cmd) ->  collectCommandCheckpoints(caze, cmd),
                    (cases) -> collectCasesCheckpoints(caze, cases));
        }
    }

    private Void collectCasesCheckpoints(ScriptAST parent, Cases cases) {
        for (Case aCase : cases.getCases()) {
            List<Statement> stms = aCase.getStatements();
            if (stms.isEmpty()) {
                checkpoints.add(ProofNodeCheckpoint.endOf(aCase, aCase, aCase.getProofNode(), Type.OPEN));
            } else {
                collectCheckpoints(aCase);
            }
        }
        return null;
    }

    private Void collectCommandCheckpoints(ScriptAST parent, Command command) {
        ProofNode node = command.getProofNode();
        // TODO : investigate needed handling
        if (node == null) {
            return null;
        }
        if(node.getChildren() == null) {
            // If the execution failed, ...
            checkpoints.add(ProofNodeCheckpoint.beginOf(parent, command, node, Type.OPEN));
            return null;
        }

        checkpoints.add(ProofNodeCheckpoint.beginOf(parent, command, node, Type.CALL));

        if (node.getChildren().size() > 1) {
            ByClause byClause = command.getByClause();
            if (byClause != null) {
                if(byClause.getStatements().isEmpty()) {
                    Token token = byClause.getOpeningBrace();
                    // TODO : review handling of by clause (end / beginning)
                    checkpoints.add(new ProofNodeCheckpoint(node.getChildren().get(0), byClause, true,
                            token.getLine(),
                            token.getCharPositionInLine() + 2, Type.OPEN));
                } else {
                    // TODO : add Support for by clasuse
                    //collectCheckpoints(byClause);
                }
            } else {
                checkpoints.add(ProofNodeCheckpoint.endOf(parent, command, node, Type.BRANCH));
            }
        } else {

            // since we know that this rule has been applied, we definitely know that
            // there is a continuation node recording the command!
            ProofNode continuation = node.getChildren().get(0);

            assert continuation.getCommand() == command;

            List<ProofNode> children = continuation.getChildren();

            if (children == null) {
                checkpoints.add(ProofNodeCheckpoint.endOf(parent, command, continuation, Type.OPEN));
            } else if (children.isEmpty()) {
                checkpoints.add(ProofNodeCheckpoint.endOf(parent, command, node, Type.CLOSED));
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
