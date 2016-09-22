package edu.kit.iti.algover.gui.components;

import edu.kit.iti.algover.Actions.ProjectTreeMouseListener;
import edu.kit.iti.algover.gui.GUICenter;
import edu.kit.iti.algover.gui.ProjectBrowserRenderer;
import edu.kit.iti.algover.model.CustomLeaf;
import edu.kit.iti.algover.model.ProjectTableTreeModel;
import edu.kit.iti.algover.model.ProjectTree;
import net.miginfocom.swing.MigLayout;
import org.jdesktop.swingx.JXTreeTable;

import javax.swing.*;
import javax.swing.tree.TreeSelectionModel;
import java.awt.event.MouseAdapter;
import java.awt.event.MouseEvent;
import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;

/**
 * Created by sarah on 9/16/16.
 */
public class CustomProjectBrowser extends JPanel {

    //JScrollPane sp = new JScrollPane();
    GUICenter center;
    JSplitPane splitpane;
    JXTreeTable treetable;
    MigLayout migLayout = new MigLayout(
                "insets 0 0 0 0",       //Layout constraints
                "[grow]",             // Column constraints
                "[grow][grow 0.9]"          // Row constraints
        );

    public CustomProjectBrowser(ProjectTree t, GUICenter center){
       // ScrollPane sp = new ScrollPane();
        this.setLayout(migLayout);

        this.setMinimumSize(super.getPreferredSize());
        //splitpane = new JSplitPane(JSplitPane.VERTICAL_SPLIT);
        //splitpane.setAutoscrolls(true);


        treetable = new JXTreeTable();
        ProjectTableTreeModel treeModel = new ProjectTableTreeModel(t);

        treetable.setTreeTableModel(treeModel);
        treetable.setTreeCellRenderer(new ProjectBrowserRenderer(this));
        treetable.getSelectionModel().setSelectionMode(TreeSelectionModel.SINGLE_TREE_SELECTION);
        treetable.addMouseListener(new ProjectTreeMouseListener(treetable, center));

        ProjectDetailView projectDetailView = new ProjectDetailView(center, this);

       /* this.addPropertyChangeListener(new PropertyChangeListener() {
            @Override
            public void propertyChange(PropertyChangeEvent evt) {
                if(evt.getPropertyName() == GUICenter.PROJECT_DIR_CHANGED){
                    setVisible(false);
                    validate();
                    repaint();
                }
                if(evt.getPropertyName() == GUICenter.PROJECT_LOADED){
                    setVisible(true);
                    validate();
                    repaint();
                }

            }
        });*/

        this.setBorder(BorderFactory.createTitledBorder("Project "+t.path));

        //JPanel panel;
        /*for(ProjectTree tr: t.children){
            panel = groupedTree(tr);
            this.add(panel, "grow, wrap");
        }*/

        this.add(treetable, "grow, wrap");
        this.add(projectDetailView, "wrap");
       // this.setVisible(true);



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
