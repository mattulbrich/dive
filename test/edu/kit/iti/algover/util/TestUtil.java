package edu.kit.iti.algover.util;

import java.util.List;

import edu.kit.iti.algover.parser.DafnyTree;

public class TestUtil {

    public static String beautify(DafnyTree tree) {
        StringBuilder sb = new StringBuilder();
        printBeautified(sb, tree, 0);
        return sb.toString();
    }

    private static void printBeautified(StringBuilder buf, DafnyTree tree, int indent) {
        List<DafnyTree> children = tree.getChildren();
        if (children == null || children.isEmpty()) {
            buf.append(tree.toString());
            return;
        }

        newLineIndent(buf, indent);

        if (!tree.isNil()) {
            buf.append("(");
            buf.append(tree.toString());
            buf.append(' ');
        }
        for (int i = 0; children != null && i < children.size(); i++) {
            DafnyTree t = children.get(i);
            if (i > 0) {
                buf.append(' ');
            }
            printBeautified(buf, t, indent+1);
        }
        if (!tree.isNil()) {
            buf.append(")");
        }
    }

    private static void newLineIndent(StringBuilder buf, int indent) {
        buf.append("\n");
        for (int i = 0; i < indent; i++) {
            buf.append(' ');
        }
    }

}
