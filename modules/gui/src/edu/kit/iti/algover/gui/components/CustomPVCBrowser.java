package edu.kit.iti.algover.gui.components;

import edu.kit.iti.algover.gui.GUICenter;
import edu.kit.iti.algover.gui.ProjectBrowserRenderer;
import edu.kit.iti.algover.model.ProjectTableTreeModel;
import edu.kit.iti.algover.model.ProjectTree;
import net.miginfocom.swing.MigLayout;
import org.jdesktop.swingx.JXTreeTable;

import javax.swing.*;
import javax.swing.tree.TreeSelectionModel;

/**
 * Panel that helps to browse the PVCs of a DafnyDecl
 * Created by sarah on 9/19/16.
 */
public class CustomPVCBrowser extends JPanel {
    GUICenter center;

    MigLayout migLayout = new MigLayout(
                "insets 0 0 0 0",       //Layout constraints
                "[grow]",             // Column constraints
                "[grow 0.7][]"          // Row constraints
        );
    public CustomPVCBrowser(GUICenter center, ProjectTree t){
        this.center = center;

        this.setLayout(migLayout);

        this.setMinimumSize(super.getPreferredSize());

        JXTreeTable treetable = new JXTreeTable();
        ProjectTableTreeModel treeModel = new ProjectTableTreeModel(t);

        treetable.setTreeTableModel(treeModel);
        treetable.setTreeCellRenderer(new ProjectBrowserRenderer(this));
        treetable.getSelectionModel().setSelectionMode(TreeSelectionModel.SINGLE_TREE_SELECTION);
        //treetable.addMouseListener(new CustomProjectBrowser.ProjectTreeMouseListener(treetable, center));

        ProjectDetailView projectDetailView = new ProjectDetailView(center, this);
        this.setBorder(BorderFactory.createTitledBorder("Project "+t.path));

        //JPanel panel;
        /*for(ProjectTree tr: t.children){
            panel = groupedTree(tr);
            this.add(panel, "grow, wrap");
        }*/

        this.add(treetable, "grow, wrap");
        this.add(projectDetailView, "wrap");
        this.setVisible(true);

    }



}
