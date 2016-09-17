package edu.kit.iti.algover.gui.components;

import edu.kit.iti.algover.gui.ProjectBrowserRenderer;
import edu.kit.iti.algover.model.ProjectTree;
import edu.kit.iti.algover.model.ProjectTreeModel;
import net.miginfocom.swing.MigLayout;

import javax.swing.*;
import java.awt.*;

/**
 * Created by sarah on 9/16/16.
 */
public class CustomProjectBrowser extends JPanel {

    JScrollPane sp = new JScrollPane();

     MigLayout migLayout = new MigLayout(
                "insets 0 0 0 0",       //Layout constraints
                "[][grow][]",               // Column constraints
                "[grow]"          // Row constraints
        );

    public CustomProjectBrowser(ProjectTree t){

        this.setLayout(migLayout);

        this.setBorder(BorderFactory.createTitledBorder("Project"));
        JPanel panel;
        for(ProjectTree tr: t.children){
            panel = groupedTree(tr);
            this.add(panel, "grow, wrap");
        }
        this.setVisible(true);



    }

    public JPanel groupedTree(ProjectTree subtree){
        JTree tree = new JTree(new ProjectTreeModel(subtree));
        tree.setRootVisible(false);
        ProjectBrowserRenderer renderer = new ProjectBrowserRenderer(this);
        tree.setCellRenderer(renderer);

       // if(subtree)
        JPanel ret = new JPanel();
        ret.setBorder(BorderFactory.createTitledBorder(subtree.name));
        ret.add(tree);
        return ret;
    }

}
