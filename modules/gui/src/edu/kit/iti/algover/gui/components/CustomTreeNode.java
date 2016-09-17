package edu.kit.iti.algover.gui.components;

import javax.swing.*;
import java.awt.*;

/**
 * Created by sarah on 9/16/16.
 */
public class CustomTreeNode extends JPanel {

    public CustomTreeNode(String name, Component parent) {
        this.setLayout(new FlowLayout());
        JLabel label = new JLabel(name);
        //JLabel stat = new JLabel(status);
        //this.setBorder(BorderFactory.createLineBorder(Color.black));
        this.add(label);
      //  this.add(stat);
    }
}
