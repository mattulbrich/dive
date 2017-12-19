package edu.kit.iti.algover.util;

import edu.kit.iti.algover.proof.ProofNode;

import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;

public final class ProofTreeUtil {

    /**
     * http://www.connorgarvey.com/blog/?p=82
     *
     * @param node
     * @return
     */
    public static String toStringTree(ProofNode node) {
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

        if (!node.getChildren().isEmpty()) {
            if (node.getChildren().size() > 1) {
                Iterator<ProofNode> it = node.getChildren().iterator();
                parentIterators.add(it);
                while (it.hasNext()) {
                    ProofNode child = it.next();
                    toStringTreeHelper(child, buffer, parentIterators);
                }
                parentIterators.remove(it);
            } else {
                ProofNode child = node.getChildren().get(0);
                toStringTreeHelper(child, buffer, parentIterators);
            }
        }

        return buffer;
    }

}
