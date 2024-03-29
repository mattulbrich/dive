/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.proof;

import edu.kit.iti.algover.rules.RuleException;
import nonnull.NonNull;

import java.util.Arrays;
import java.util.List;
import java.util.Optional;
import java.util.Stack;

/**
 * Created by Philipp on 27.08.2017.
 */
public class ProofNodeSelector {

    private final int[] path;

    public ProofNodeSelector(int... path) {
        this.path = path;
    }

    public ProofNodeSelector(ProofNodeSelector prefix, int... path) {
        this(concatArrays(prefix.path, path));
    }

    private static int[] concatArrays(int[] prefix, int[] suffix) {
        int[] result = new int[prefix.length + suffix.length];
        System.arraycopy(prefix, 0, result, 0, prefix.length);
        System.arraycopy(suffix, 0, result, prefix.length, suffix.length);
        return result;
    }

    public ProofNodeSelector(ProofNode proofNode) {
        this(calculatePathFromNode(proofNode));
    }

    private static int[] calculatePathFromNode(ProofNode proofNode) {
        Stack<Integer> pathStack = new Stack<>();
        ProofNode node = proofNode;
        while (node.getParent() != null) {
            int childIndex = node.getParent().getSuccessors().indexOf(node);
            if (childIndex < 0) {
                throw new RuntimeException("This should not happen. Invalid ProofNode structure!");
            }
            pathStack.push(childIndex);
            node = node.getParent();
        }
        int[] path = new int[pathStack.size()];
        for (int i = 0; i < path.length; i++) {
            path[i] = pathStack.pop();
        }
        return path;
    }

    public Optional<ProofNode> optionalGet(Proof proof) {
        try {
            return Optional.of(get(proof));
        } catch (RuleException e) {
            return Optional.empty();
        }
    }

    public ProofNode get(@NonNull Proof proof) throws RuleException {
        return getNode(proof.getProofRoot());
    }

    /**
     * Follow the path of this selector to select a proof node starting at the given node.
     * The node is returned in case the path is empty.
     *
     * @param node the start node for the navigation
     * @return the selected node from node on
     * @throws RuleException if the selection cannot be made for index reasons.
     */
    public ProofNode getNode(@NonNull ProofNode node) throws RuleException {
        ProofNode currentNode = node;
        for (int i = 0; i < path.length; i++) {
            List<ProofNode> children = currentNode.getChildren();
            if (children == null) {
                throw new RuleException("Cannot select proof node. Current node has 'null' children.");
            }
            if (children.size() <= path[i]) {
                throw new RuleException("Cannot select proof node. Current node only has "
                        + children.size() + " children, but proof child "
                        + path[i] + " was to be visited. (item " + i + " in path " + toString() + ")");
            }
            currentNode = children.get(path[i]);
        }
        return currentNode;
    }

    public ProofNode followAsFarAsPossible(@NonNull ProofNode node) {
        ProofNode currentNode = node;
        for (int i = 0; i < path.length; i++) {
            List<ProofNode> children = currentNode.getChildren();
            if (children == null) {
                return currentNode;
            }
            if (children.size() <= path[i]) {
                return currentNode;
            }
            currentNode = children.get(path[i]);
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

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (!(o instanceof ProofNodeSelector)) return false;

        ProofNodeSelector that = (ProofNodeSelector) o;

        return Arrays.equals(path, that.path);
    }

    @Override
    public int hashCode() {
        return Arrays.hashCode(path);
    }

    public int[] getPath() {
        return path;
    }

    public ProofNodeSelector getParentSelector() {
        if(path.length < 1) {
            return null;
        }
        int[] newPath = new int[path.length - 1];
        System.arraycopy(path, 0, newPath, 0, newPath.length);
        return new ProofNodeSelector(newPath);
    }
}
