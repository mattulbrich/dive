package edu.kit.iti.algover.gui.components;

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

/**
 * Created by sarah on 9/16/16.
 */
public class CustomProjectBrowser extends JPanel {

    //JScrollPane sp = new JScrollPane();
    GUICenter center;


     MigLayout migLayout = new MigLayout(
                "insets 0 0 0 0",       //Layout constraints
                "[grow]",             // Column constraints
                "[grow 0.7][]"          // Row constraints
        );

    public CustomProjectBrowser(ProjectTree t, GUICenter center){
       // ScrollPane sp = new ScrollPane();
        this.setLayout(migLayout);

        this.setMinimumSize(super.getPreferredSize());

        JXTreeTable treetable = new JXTreeTable();
        ProjectTableTreeModel treeModel = new ProjectTableTreeModel(t);

        treetable.setTreeTableModel(treeModel);
        treetable.setTreeCellRenderer(new ProjectBrowserRenderer(this));
        treetable.getSelectionModel().setSelectionMode(TreeSelectionModel.SINGLE_TREE_SELECTION);
        treetable.addMouseListener(new ProjectTreeMouseListener(treetable, center));

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

    private static class ProjectTreeMouseListener extends MouseAdapter {
        private final JXTreeTable treetable;
        private final GUICenter center;

        public ProjectTreeMouseListener(JXTreeTable treetable, GUICenter center) {
            this.treetable = treetable;
            this.center = center;
        }

        @Override
        public void mouseClicked(MouseEvent e) {

            if(e.getClickCount() == 2) {
                ProjectTree lastPathComponent = (ProjectTree) treetable.getPathForLocation(e.getX(), e.getY()).getLastPathComponent();
                if(lastPathComponent instanceof CustomLeaf){
                    CustomLeaf l = (CustomLeaf) lastPathComponent;
                    center.setLoadedDafnySrc(l.getData().getFile().getAbsoluteFile());
                    center.setSelectedProjectSubTree(l);

                }else{
                    center.setSelectedProjectSubTree(lastPathComponent);
                }
            }

        }
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
