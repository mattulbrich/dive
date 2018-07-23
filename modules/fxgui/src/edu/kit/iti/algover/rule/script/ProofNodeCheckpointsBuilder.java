package edu.kit.iti.algover.rule.script;

import edu.kit.iti.algover.proof.Proof;
import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.proof.ProofNodeSelector;
import edu.kit.iti.algover.rules.RuleException;
import edu.kit.iti.algover.script.ast.*;
import edu.kit.iti.algover.script.parser.DefaultASTVisitor;

import java.util.ArrayList;
import java.util.Collections;
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
    private List<ProofNode> lastHandledNodes;
    private List<ProofNodeSelector> lastHandledSelectors;
    private int inCase = 0;

    private ProofNodeCheckpointsBuilder(ProofNode rootProofNode) {
        this.rootProofNode = rootProofNode;
        lastHandledNodes = new ArrayList<>(Collections.singletonList(rootProofNode));
        lastHandledSelectors = new ArrayList<>(Collections.singletonList(new ProofNodeSelector()));
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
                if(inCase == lastHandledNodes.size() - 1) {
                    lastHandledNodes.set(lastHandledNodes.size() - 1, selectorBefore.getNode(rootProofNode));
                    lastHandledSelectors.set(lastHandledSelectors.size() - 1, selectorBefore);
                } else {
                    lastHandledNodes.add(selectorBefore.getNode(rootProofNode));
                    lastHandledSelectors.add(selectorBefore);
                }
            } catch (RuleException ex) {
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
        for (int i = 0; lastHandledNodes.size() > 0 && i < lastHandledNodes.get(lastHandledNodes.size() - 1).getChildren().size(); ++i) {
            //TODO only label matching no sequent matching supported as of yet
            if (simpleCaseStatement.getGuard().getText().
                    substring(6, simpleCaseStatement.getGuard().getText().length() - 1).
                    equals(lastHandledNodes.get(lastHandledNodes.size() - 1).getChildren().get(i).getLabel())) {
                selectedChildIdx = i;
            }
        }
        if (selectedChildIdx != -1) {
            ProofNodeSelector selector = new ProofNodeSelector(lastHandledSelectors.get(lastHandledSelectors.size() - 1), selectedChildIdx);
            Position position = simpleCaseStatement.getStartPosition();
            Position guardPosition = simpleCaseStatement.getGuard().getEndPosition();
            Position caretPosition = new Position(position.getLineNumber() + 1, 2);
            checkpoints.add(new ProofNodeCheckpoint(selector, position, caretPosition));
        }
        // TODO: Find out how to get a ProofNodeSelector out of a specific case (rudimentary solution above)
        // (so that you can click inside an empty case to see what it's sequent state looks like)
        // (same for the CaseStatement visit)
        inCase++;
        simpleCaseStatement.getBody().accept(this);
        if(lastHandledNodes.size() > 0) {
            lastHandledSelectors.remove(lastHandledSelectors.size() - 1);
            lastHandledNodes.remove(lastHandledNodes.size() - 1);
        }
        inCase--;
        return null;
    }

    @Override
    public Void visit(CaseStatement caseStatement) {
        inCase++;
        caseStatement.getBody().accept(this);
        lastHandledSelectors.remove(lastHandledSelectors.size() - 1);
        lastHandledNodes.remove(lastHandledNodes.size() - 1);
        inCase--;
        return null;
    }

    private ProofNodeSelector findSelectorPointingTo(ProofNodeSelector pathSoFar, ProofNode proofNode, ASTNode node) {
        if (rlyContains(proofNode.getMutator(), node)) {
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

    private boolean rlyContains(List<ASTNode> l, ASTNode n) {
        for(ASTNode n1 : l) {
            if(n == n1) return true;
        }
        return false;
    }

}
