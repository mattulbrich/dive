package edu.kit.iti.algover.rule.script;

import edu.kit.iti.algover.proof.Proof;
import edu.kit.iti.algover.script.ast.*;
import edu.kit.iti.algover.script.parser.DefaultASTVisitor;
import edu.kit.iti.algover.util.Pair;

import java.util.ArrayList;
import java.util.List;

public class ProofNodeCheckpointsBuilder extends DefaultASTVisitor<Void> {

    public static List<ProofNodeCheckpoint> build(Proof proof) {
        ProofNodeCheckpointsBuilder builder = new ProofNodeCheckpointsBuilder();
        if (proof.getProofScript() == null) {
            return builder.checkpoints;
        }
        proof.getProofScript().accept(builder);
        return builder.checkpoints;
    }

    private final List<ProofNodeCheckpoint> checkpoints;

    private ProofNodeCheckpointsBuilder() {
        checkpoints = new ArrayList<>();
    }

    public static List<ProofNodeCheckpoint> build(ProofScript script) {
        ProofNodeCheckpointsBuilder builder = new ProofNodeCheckpointsBuilder();
        if (script == null) {
            return builder.checkpoints;
        }
        script.accept(builder);
        return builder.checkpoints;
    }

    @Override
    public Void visit(ProofScript proofScript) {
        return proofScript.getBody().accept(this);
    }

    @Override
    @SuppressWarnings("unchecked") // REVIEW: Repair this as soon as the scripts are correctly generically treated
    public Void visit(Statements statements) {
        statements.forEach(node -> node.accept(this));
        return null;
    }

    @Override
    public Void visit(CallStatement call) {
        checkpoints.add(new ProofNodeCheckpoint(call.getEndPosition(), call));
        return null;
    }

    @Override
    public Void visit(CasesStatement cases) {
        cases.getCases().forEach(caze -> caze.accept(this));
        return null;
    }

    @Override
    @SuppressWarnings("unchecked") // REVIEW: Repair this as soon as the scripts are correctly generically treated
    public Void visit(SimpleCaseStatement simpleCaseStatement) {
        checkpoints.add(new ProofNodeCheckpoint(simpleCaseStatement.getGuard().getEndPosition(), simpleCaseStatement));
        simpleCaseStatement.getBody().forEach(statement -> statement.accept(this));
        return null;
    }

    @Override
    public Void visit(CaseStatement caseStatement) {
        caseStatement.getBody().accept(this);
        return null;
    }
}
