package edu.kit.iti.algover.gui;

import javax.swing.*;
import javax.swing.tree.DefaultMutableTreeNode;
import java.awt.*;

/**
 * Created by Azadeh Shirvanian on 27.09.2016.
 */
public class SettingsWindow extends JFrame{

    GUICenter center;
    JTree proverTree;
    JPanel rightPanel;
    JPanel buttonPanel;
    JSpinner timeoutSpinner;
    JButton okButton = new JButton("OK");
    JButton applyButton = new JButton("Apply");
    JButton cancelButton = new JButton("Cancel");

    public SettingsWindow (GUICenter center)
    {
        this.center = center;
        createSettingsWindow();
    }


    public void createSettingsWindow(){

        this.setLayout(new BorderLayout());
        this.setDefaultCloseOperation(JFrame.DISPOSE_ON_CLOSE);
        this.setTitle("Prover Settings");


        DefaultMutableTreeNode root = new DefaultMutableTreeNode("Provers");
        DefaultMutableTreeNode z3Node = new DefaultMutableTreeNode("Z3");
        DefaultMutableTreeNode dafnyNode = new DefaultMutableTreeNode("Dafny");
        DefaultMutableTreeNode keyNode = new DefaultMutableTreeNode("KeY");

        root.add(z3Node);
        root.add(dafnyNode);
        root.add(keyNode);

        proverTree = new JTree(root);
        this.add(proverTree, BorderLayout.WEST);

        this.pack();
        this.setLocationRelativeTo(null);
    }

}
