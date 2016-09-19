package edu.kit.iti.algover.gui.components;

import javax.swing.*;
import java.awt.*;

/**
 * Created by sarah on 9/16/16.
 */
public class CustomTreeNode extends JPanel {

    public CustomTreeNode(String name, Component parent)
    {
        this.setBackground(Color.WHITE);

        JLabel label = new JLabel(name);
        this.add(label);

    }
}
