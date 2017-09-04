package edu.kit.iti.algover.proof;

import edu.kit.iti.algover.rules.RuleException;

/**
 * Created by Philipp on 27.08.2017.
 */
public class ProofNodeSelector {

    private final byte[] path;

    public ProofNodeSelector(byte... path) {
        this.path = path;
    }

    public ProofNode get(Proof proof) throws RuleException {
        return getNode(proof.getProofRoot());
    }

    private ProofNode getNode(ProofNode node) throws RuleException {
        ProofNode currentNode = node;
        for (int i = 0; i < path.length; i++) {
            if (currentNode.getChildren().size() <= path[i]) {
                throw new RuleException("Cannot select proof node. Proof node only has "
                        + currentNode.getChildren().size() + " children, but proof child No. "
                        + path[i] + " was to be visited. (item " + i + " in path " + toString() + ")");
            }
            currentNode = currentNode.getChildren().get(path[i]);
        }
        return currentNode;
    }

    public String toString() {
        if (path.length == 0) {
            return "<root>";
        }
        StringBuilder builder = new StringBuilder();
        for (int i = 0; i < path.length; i++) {
            if (i > 0) {
                builder.append(".");
            }
            builder.append(path[i]);
        }
        return builder.toString();
    }

}
