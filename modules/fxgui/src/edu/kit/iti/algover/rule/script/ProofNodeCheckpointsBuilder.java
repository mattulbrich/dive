package edu.kit.iti.algover.rule.script;

import edu.kit.iti.algover.proof.Proof;
import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.proof.ProofNodeSelector;
import edu.kit.iti.algover.rules.RuleException;
import edu.kit.iti.algover.script.ast.*;
import edu.kit.iti.algover.script.parser.DefaultASTVisitor;

import java.util.ArrayList;
import java.util.List;

public class ProofNodeCheckpointsBuilder extends DefaultASTVisitor<Void> {

    public static List<ProofNodeCheckpoint> build(Proof proof) {
        ProofNodeCheckpointsBuilder builder = new ProofNodeCheckpointsBuilder(proof.getProofRoot());
        if (proof.getProofScript() == null) {
            return builder.checkpoints;
        }
        proof.getProofScript().accept(builder);
        return builder.checkpoints;
    }

    private final List<ProofNodeCheckpoint> checkpoints;
    private final ProofNode rootProofNode;
    private ProofNode lastHandledNode;
    private ProofNodeSelector lastHandledSelector;

    private ProofNodeCheckpointsBuilder(ProofNode rootProofNode) {
        this.rootProofNode = rootProofNode;
        lastHandledNode = rootProofNode;
        lastHandledSelector = new ProofNodeSelector();
        checkpoints = new ArrayList<>();
        checkpoints.add(new ProofNodeCheckpoint(new ProofNodeSelector(), new Position(0, 0), new Position(0, 0)));
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
            try {
                lastHandledNode = selectorBefore.getNode(rootProofNode);
                lastHandledSelector = selectorBefore;
            } catch(RuleException ex) {
                System.out.println("Could not select last handled node.");
            }
            checkpoints.add(new ProofNodeCheckpoint(selector, position, new Position(position.getLineNumber() + 1, 0)));
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
        int selectedChildIdx = -1;
        for(int i = 0; i < lastHandledNode.getChildren().size(); ++i) {
            //TODO only label matching no sequent matching supported as of yet
            if(simpleCaseStatement.getGuard().getText().
                    substring(1, simpleCaseStatement.getGuard().getText().length() - 1).
                    equals(lastHandledNode.getChildren().get(i).getLabel())) {
                selectedChildIdx = i;
            }
        }
        if(selectedChildIdx != -1) {
            ProofNodeSelector selector = new ProofNodeSelector(lastHandledSelector, selectedChildIdx);
            Position position = simpleCaseStatement.getStartPosition();
            Position guardPosition = simpleCaseStatement.getGuard().getEndPosition();
            Position caretPosition = new Position(position.getLineNumber() + 1, 2);
            checkpoints.add(new ProofNodeCheckpoint(selector, position, caretPosition));
        }
        // TODO: Find out how to get a ProofNodeSelector out of a specific case (rudimentary solution above)
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
