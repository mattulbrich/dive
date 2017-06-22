package edu.kit.iti.algover.gui.components;

import edu.kit.iti.algover.Actions.PVCSelectionMouseListener;
import edu.kit.iti.algover.gui.GUICenter;
import edu.kit.iti.algover.gui.ProjectBrowserPanel;
import edu.kit.iti.algover.model.CustomLeaf;
import edu.kit.iti.algover.model.PVCTreeModel;
import net.miginfocom.swing.MigLayout;
import org.jdesktop.swingx.JXTree;

import javax.swing.*;
import java.awt.*;

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
    public CustomPVCBrowser(GUICenter center, CustomLeaf l){
        this.center = center;

        this.setLayout(migLayout);

        this.setMinimumSize(super.getPreferredSize());

        //JXTreeTable treetable = new JXTreeTable();

        PVCTreeModel model = new PVCTreeModel(center.getLoadedProject(), center.getProjectTreeModel());
        JXTree tr = new JXTree(model);

        tr.setRootVisible(true);
        tr.addMouseListener(new PVCSelectionMouseListener(center, tr));
        this.setBorder(BorderFactory.createTitledBorder("Project "));

        //tr.addMouseListener(new ProjectTreeMouseListener());
        //ProjectTree tree = center.getSelectedProjectSubTree();
        //System.out.println(tree);
        //System.out.println();

        //ProjectTableTreeModel treeModel = new ProjectTableTreeModel(center.getProjectTreeModel());
        //treetable.setTreeTableModel(treeModel);

        //treetable.expandPath(center.getSelectedPath());
        //treetable.setTreeCellRenderer(new ProjectBrowserRenderer(this));

        //treetable.getSelectionModel().setSelectionMode(TreeSelectionModel.SINGLE_TREE_SELECTION);

        //treetable.setRootVisible(true);
        //treetable.addMouseListener(new ProjectTreeMouseListener(treetable, center));

        //this.setBorder(BorderFactory.createTitledBorder("Project "+tree.path));

        back.addActionListener(e -> {
            if(e.getActionCommand().equals("Back to ProjectBrowser")){
                CardLayout cl = (CardLayout)center.getMainwindow().getpPanel().cards.getLayout();
                cl.show(center.getMainwindow().getpPanel().cards, ProjectBrowserPanel.PR_BROWSER);
            }
        });
        this.add(back, "grow, wrap");
        this.add(tr, "grow, wrap");
        //this.add(treetable, "grow, wrap");
        this.setVisible(true);

    }



}
