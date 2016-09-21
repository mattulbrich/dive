package edu.kit.iti.algover.gui.components;

import edu.kit.iti.algover.gui.ButtonListener;
import edu.kit.iti.algover.gui.GUICenter;
import edu.kit.iti.algover.gui.ProjectBrowserPanel;
import edu.kit.iti.algover.gui.ProjectBrowserRenderer;
import edu.kit.iti.algover.model.ProjectTableTreeModel;
import edu.kit.iti.algover.model.ProjectTree;
import net.miginfocom.swing.MigLayout;
import org.jdesktop.swingx.JXTreeTable;

import javax.swing.*;
import javax.swing.tree.TreeSelectionModel;
import java.awt.*;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;

/**
 * Panel that helps to browse the PVCs of a DafnyDecl
 * Created by sarah on 9/19/16.
 */
public class CustomPVCBrowser extends JPanel {
    GUICenter center;
    JButton back = new JButton("Back to ProjectBrowser");

    MigLayout migLayout = new MigLayout(
                "insets 0 0 0 0",       //Layout constraints
                "[grow]",             // Column constraints
                "[0.3][grow]"          // Row constraints
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
        treetable.setRootVisible(true);

        this.setBorder(BorderFactory.createTitledBorder("Project "+t.path));

        back.addActionListener(e -> {
            if(e.getActionCommand().equals("Back to ProjectBrowser")){
                CardLayout cl = (CardLayout)center.getMainwindow().getpPanel().cards.getLayout();
                cl.show(center.getMainwindow().getpPanel().cards, ProjectBrowserPanel.PR_BROWSER);
            }
        });
        this.add(back, "grow, wrap");
        this.add(treetable, "grow, wrap");
        this.setVisible(true);

    }



}
