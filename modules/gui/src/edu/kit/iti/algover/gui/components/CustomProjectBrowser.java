package edu.kit.iti.algover.gui.components;

import edu.kit.iti.algover.gui.ProjectBrowserRenderer;
import edu.kit.iti.algover.model.ProjectTableTreeModel;
import edu.kit.iti.algover.model.ProjectTree;
import edu.kit.iti.algover.model.ProjectTreeModel;
import net.miginfocom.swing.MigLayout;
import org.jdesktop.swingx.JXTreeTable;

import javax.swing.*;
import javax.swing.border.CompoundBorder;
import javax.swing.border.TitledBorder;
import java.awt.*;

/**
 * Created by sarah on 9/16/16.
 */
public class CustomProjectBrowser extends JPanel {

    //JScrollPane sp = new JScrollPane();



     MigLayout migLayout = new MigLayout(
                "insets 0 0 0 0",       //Layout constraints
                "[grow]",             // Column constraints
                "[grow 0.7][]"          // Row constraints
        );

    public CustomProjectBrowser(ProjectTree t){
       // ScrollPane sp = new ScrollPane();
        this.setLayout(migLayout);

        this.setMinimumSize(super.getPreferredSize());

        JXTreeTable treetable = new JXTreeTable();
        treetable.setTreeTableModel(new ProjectTableTreeModel(t));
        treetable.setTreeCellRenderer(new ProjectBrowserRenderer(this));

        ProjectDetailView projectDetailView = new ProjectDetailView();
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

    /*public JPanel groupedTree(ProjectTree subtree){
        JXTreeTable treetable = new JXTreeTable();
        treetable.setTreeTableModel(new ProjectTableTreeModel(subtree));
        treetable.setTreeCellRenderer(new ProjectBrowserRenderer(this));

        JPanel ret = new JPanel();
        ret.setLayout(new BorderLayout());

        TitledBorder titledBorder = BorderFactory.createTitledBorder(subtree.name);
        ret.setBorder(titledBorder);
        ret.add(treetable, BorderLayout.CENTER);

        return ret;
    }*/

}
