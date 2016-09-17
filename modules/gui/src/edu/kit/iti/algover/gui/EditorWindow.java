package edu.kit.iti.algover.gui;


import net.miginfocom.swing.MigLayout;

import java.awt.*;
import javax.swing.*;

/**
 * EditorWindow with MigLayout consists of a menu bar, a toolbar,
 * a panel for the text area inside a tabbed pane, and a footer panel.
 *
 * Created by sony on 06.09.2016.
 */

public class EditorWindow extends JFrame
{
    /*GridBagConstraints c = new GridBagConstraints();
    GridBagLayout gridbag = new GridBagLayout();*/



    public EditorWindow (GUICenter center) {

        MenuBar menuBar = new MenuBar(center);
        ToolBar toolbar = new ToolBar(center);
        EditorPanel panel = new EditorPanel(center);
        FooterPanel footerPanel = new FooterPanel(center);

        MigLayout migLayout = new MigLayout(
                "insets 0 0 0 0",       //Layout constraints
                "[grow]",               // Column constraints
                "[][][grow][]"          // Row constraints
        );

        setTitle("AlgoVer");
        setDefaultCloseOperation( JFrame.EXIT_ON_CLOSE );
        setBounds(250, 120, 300, 300);
        setLayout(migLayout);

        add(menuBar, "growx, wrap");
        add(toolbar, "growx, wrap");
        add(panel, "grow, wrap");
        add(footerPanel, "growx, wrap");


    }
}
