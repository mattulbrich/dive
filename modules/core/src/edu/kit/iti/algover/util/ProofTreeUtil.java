/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.util;

import edu.kit.iti.algover.proof.ProofNode;
import nonnull.NonNull;

import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;

/**
 * A collection of static methods for proof trees / proof nodes.
 *
 * @author Sarah Grebing
 */
public final class ProofTreeUtil {

    private ProofTreeUtil() {
        // not to be instantiated
    }

    /**
     * Render a proof node into a multi-line string that shows the tree structure of the
     * proof.
     *
     * See also http://www.connorgarvey.com/blog/?p=82.
     *
     * @param node the node to print the tree for
     * @return a multi-line string representation of the node
     */
    public static @NonNull String toStringTree(@NonNull ProofNode node) {
        final StringBuilder buffer = new StringBuilder();
        return toStringTreeHelper(node, buffer, new LinkedList<Iterator<ProofNode>>()).toString();
    }

    private static String toStringTreeDrawLines(List<Iterator<ProofNode>> parentIterators, boolean amLast) {
        StringBuilder result = new StringBuilder();
        Iterator<Iterator<ProofNode>> it = parentIterators.iterator();
        while (it.hasNext()) {
            Iterator<ProofNode> anIt = it.next();
            if (anIt.hasNext() || (!it.hasNext() && amLast)) {
                result.append("   |");
            } else {
                result.append("    ");
            }
        }
        return result.toString();
    }

    private static StringBuilder toStringTreeHelper(ProofNode node, StringBuilder buffer, List<Iterator<ProofNode>>
            parentIterators) {
        if (!parentIterators.isEmpty()) {
            boolean amLast = !parentIterators.get(parentIterators.size() - 1).hasNext();
            buffer.append("\n");
            String lines = toStringTreeDrawLines(parentIterators, amLast);
            buffer.append(lines);
            buffer.append("\n");
            buffer.append(lines);
            buffer.append("- ");
        }
        buffer.append(node.toString());

        List<ProofNode> children = node.getChildren();
        if (children != null && !children.isEmpty()) {
            if (children.size() > 1) {
                Iterator<ProofNode> it = children.iterator();
                parentIterators.add(it);
                while (it.hasNext()) {
                    ProofNode child = it.next();
                    toStringTreeHelper(child, buffer, parentIterators);
                }
                parentIterators.remove(it);
            } else {
                ProofNode child = children.get(0);
                toStringTreeHelper(child, buffer, parentIterators);
            }
        }

        return buffer;
    }

}
