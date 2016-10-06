package edu.kit.iti.algover.gui;

import edu.kit.iti.algover.model.ProjectTreeAdaptor;
import edu.kit.iti.algover.project.Project;
import edu.kit.iti.algover.project.ProjectBuilder;
import org.jdesktop.swingx.JXTreeTable;

import javax.swing.*;
import javax.swing.tree.DefaultMutableTreeNode;
import javax.swing.tree.TreePath;
import java.awt.*;
import java.io.File;

/** This panel includes a scroll pane, which contains a sample tree.
 * Problem: Hiding the root hides the whole tree.
 *
 * Created by sony on 10.09.2016.
 */
@Deprecated
public class TreePanel extends JPanel {

    String testDir = "modules/core/test-res/edu/kit/iti/algover/project";

/*
    DefaultMutableTreeNode root = new DefaultMutableTreeNode("Root");
    DefaultMutableTreeNode class1 = new DefaultMutableTreeNode("Class 1");
    DefaultMutableTreeNode class2 = new DefaultMutableTreeNode("Class 2");
    DefaultMutableTreeNode class3 = new DefaultMutableTreeNode("General Lemma");

    JTree tree = new JTree (root);
    JScrollPane sc = new JScrollPane(tree);*/

    JXTreeTable table = new JXTreeTable();

    public TreePanel (GUICenter center) {

        ProjectTreeAdaptor adapt = new ProjectTreeAdaptor(prepare());
        table.setTreeTableModel(adapt);
        table.setRootVisible(true);
        table.setOverwriteRendererIcons(true);
        //root.add(class1);
        //root.add(class2);
        //root.add(class3);

        //class1.add(new DefaultMutableTreeNode("Method 1"));
        //class1.add(new DefaultMutableTreeNode("Method 2"));
        //class1.add(new DefaultMutableTreeNode("Function 1"));

        //class2.add(new DefaultMutableTreeNode("Method 1"));
        //class2.add(new DefaultMutableTreeNode("Method 2"));
        //class2.add(new DefaultMutableTreeNode("Method 3"));

        //tree.setRootVisible(false);
        //tree.setShowsRootHandles(true);

        setLayout(new BorderLayout());
        add(table, BorderLayout.CENTER);
       // add(sc, BorderLayout.CENTER);
    }

     public Project prepare(){

        final File f1 = new File(testDir);

        ProjectBuilder pb = new ProjectBuilder();

        Project p = null;

        try {
            p = pb.buildProject(f1);
        } catch (Exception e) {
            e.printStackTrace();
        }
        return p;

    }
}
