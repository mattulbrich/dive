package edu.kit.iti.algover.gui;


import edu.kit.iti.algover.gui.components.CustomTreeNode;
import edu.kit.iti.algover.model.CustomLeaf;

import javax.swing.*;
import javax.swing.tree.DefaultTreeCellRenderer;
import javax.swing.tree.TreeCellRenderer;
import java.awt.*;
import java.awt.event.MouseAdapter;
import java.awt.event.MouseEvent;

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
            Icon i;
            if(val.getStatus() == "Test"){
                java.net.URL imageURL = ProjectBrowserRenderer.class.getResource("proof.png");
               // i = new ImageIcon("../res/proof.png");
                if (imageURL != null) {
                    i = new ImageIcon(imageURL);
                }else{
                    i = new ImageIcon();
                }
            }else{
                 i = new ImageIcon("../res/stop.png");
            }
            JLabel l = new JLabel(val.getName(), i, JLabel.HORIZONTAL);
            return l;
        }else {

            CustomTreeNode customTreeNode = new CustomTreeNode(value.toString(), this.parent);

            return customTreeNode;
        }
    }

}
