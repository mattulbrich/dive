package edu.kit.iti.algover.gui;


import edu.kit.iti.algover.gui.components.CustomTreeNode;
import edu.kit.iti.algover.model.CustomLeaf;

import javax.swing.*;
import javax.swing.tree.DefaultTreeCellRenderer;
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
       // Component c = super.getTreeCellRendererComponent(tree, value, selected, expanded, leaf, row, hasFocus);


        if(leaf){
            CustomLeaf val = (CustomLeaf) value;


            /*JLabel custom = new JLabel(val.getName());
            JLabel stat = new JLabel(val.getStatus());
            JPanel leafPanel = new JPanel();
            BoxLayout bl = new BoxLayout(leafPanel, BoxLayout.LINE_AXIS);
            leafPanel.setLayout(bl);

            Dimension min = new Dimension(custom.getWidth()+10, custom.getHeight());
            Dimension pref = new Dimension(custom.getWidth()+100, custom.getHeight());
            Dimension max = new Dimension(custom.getWidth()+150, custom.getHeight());

            leafPanel.add(custom);
            leafPanel.add(new Box.Filler(min, pref, max));
            leafPanel.add(stat);
            leafPanel.setBackground(Color.WHITE);*/
            //return leafPanel;
            return new JLabel(val.getName());
        }else {
            //return c;

            CustomTreeNode customTreeNode = new CustomTreeNode(value.toString(), this.parent);

            return customTreeNode;
        }
    }

}
