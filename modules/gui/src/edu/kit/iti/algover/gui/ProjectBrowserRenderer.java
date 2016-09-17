package edu.kit.iti.algover.gui;


import edu.kit.iti.algover.gui.components.CustomTreeNode;
import edu.kit.iti.algover.model.CustomLeaf;

import javax.swing.*;
import javax.swing.tree.TreeCellRenderer;
import java.awt.*;

/**
 * Created by sarah on 9/16/16.
 */
public class ProjectBrowserRenderer implements TreeCellRenderer {

    Component parent;
    public ProjectBrowserRenderer(Component parent){
        this.parent = parent;
    }

    @Override
    public Component getTreeCellRendererComponent(JTree tree,
                                                  Object value,
                                                  boolean selected,
                                                  boolean expanded,
                                                  boolean leaf,
                                                  int row,
                                                  boolean hasFocus) {

        if(leaf){
            CustomLeaf val = (CustomLeaf) value;

            JLabel custom = new JLabel(val.getName());
            JLabel stat = new JLabel(val.getStatus());

//            custom.setBackground(new Color(100, 75, 90));
            JPanel leafPanel = new JPanel();
            FlowLayout fl = new FlowLayout();

            leafPanel.setLayout(fl);
            leafPanel.add(custom);
            leafPanel.add(stat);
            return leafPanel;
        }else {
            return new CustomTreeNode(value.toString(), this.parent);
        }
    }

}
