package edu.kit.iti.algover.gui;

import javax.swing.*;
import javax.swing.tree.DefaultMutableTreeNode;
import javax.swing.tree.TreePath;
import java.awt.*;

/** This panel includes a scroll pane, which contains a sample tree.
 * Problem: Hiding the root hides the whole tree.
 *
 * Created by sony on 10.09.2016.
 */
public class TreePanel extends JPanel {

    DefaultMutableTreeNode root = new DefaultMutableTreeNode("Root");
    DefaultMutableTreeNode class1 = new DefaultMutableTreeNode("Class 1");
    DefaultMutableTreeNode class2 = new DefaultMutableTreeNode("Class 2");
    DefaultMutableTreeNode class3 = new DefaultMutableTreeNode("General Lemma");

    JTree tree = new JTree (root);
    JScrollPane sc = new JScrollPane(tree);

    public TreePanel () {

        root.add(class1);
        root.add(class2);
        root.add(class3);

        class1.add(new DefaultMutableTreeNode("Method 1"));
        class1.add(new DefaultMutableTreeNode("Method 2"));
        class1.add(new DefaultMutableTreeNode("Function 1"));

        class2.add(new DefaultMutableTreeNode("Method 1"));
        class2.add(new DefaultMutableTreeNode("Method 2"));
        class2.add(new DefaultMutableTreeNode("Method 3"));

        //tree.setRootVisible(false);
        //tree.setShowsRootHandles(true);

        setLayout(new BorderLayout());
        add(sc, BorderLayout.CENTER);
    }
}
