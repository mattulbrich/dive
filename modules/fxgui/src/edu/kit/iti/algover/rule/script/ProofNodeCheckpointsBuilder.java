package edu.kit.iti.algover.rule.script;

import edu.kit.iti.algover.proof.Proof;
import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.proof.ProofNodeSelector;
import edu.kit.iti.algover.script.ast.*;
import edu.kit.iti.algover.script.parser.DefaultASTVisitor;

import java.util.ArrayList;
import java.util.List;

public class ProofNodeCheckpointsBuilder extends DefaultASTVisitor<Void> {

    public static List<ProofNodeCheckpoint> build(Proof proof) {
        ProofNodeCheckpointsBuilder builder = new ProofNodeCheckpointsBuilder(proof.getProofRoot());
        proof.getProofScript().accept(builder);
        return builder.checkpoints;
    }

    private final List<ProofNodeCheckpoint> checkpoints;
    private final ProofNode rootProofNode;

    private ProofNodeCheckpointsBuilder(ProofNode rootProofNode) {
        this.rootProofNode = rootProofNode;
        checkpoints = new ArrayList<>();
        checkpoints.add(new ProofNodeCheckpoint(new ProofNodeSelector(), new Position(0, 0)));
    }

    @Override
    public Void visit(ProofScript proofScript) {
        return proofScript.getBody().accept(this);
    }

    @Override
    public Void visit(Statements statements) {
        statements.forEach(node -> node.accept(this));
        return null;
    }

    @Override
    public Void visit(CallStatement call) {
        ProofNodeSelector selectorBefore = findSelectorPointingTo(new ProofNodeSelector(), rootProofNode, call);
        if (selectorBefore != null) {
            ProofNodeSelector selector = new ProofNodeSelector(selectorBefore, 0);
            Position position = call.getEndPosition();
            checkpoints.add(new ProofNodeCheckpoint(selector, position));
        }
        return null;
    }

    @Override
    public Void visit(CasesStatement cases) {
        cases.getCases().forEach(caze -> caze.accept(this));
        return null;
    }

    @Override
    public Void visit(SimpleCaseStatement simpleCaseStatement) {
        Position position = simpleCaseStatement.getGuard().getEndPosition();
        // TODO: Find out how to get a ProofNodeSelector out of a specific case
        // (so that you can click inside an empty case to see what it's sequent state looks like)
        // (same for the CaseStatement visit)
        simpleCaseStatement.getBody().accept(this);
        return null;
    }

    @Override
    public Void visit(CaseStatement caseStatement) {
        caseStatement.getBody().accept(this);
        return null;
    }

    private ProofNodeSelector findSelectorPointingTo(ProofNodeSelector pathSoFar, ProofNode proofNode, ASTNode node) {
        if (proofNode.getMutator().contains(node)) {
            return pathSoFar;
        } else {
            for (int i = 0; i < proofNode.getChildren().size(); i++) {
                ProofNode child = proofNode.getChildren().get(i);
                ProofNodeSelector subselector = findSelectorPointingTo(new ProofNodeSelector(pathSoFar, i), child, node);
                if (subselector != null) {
                    return subselector;
                }
            }
            return null;
        }
    }

}
