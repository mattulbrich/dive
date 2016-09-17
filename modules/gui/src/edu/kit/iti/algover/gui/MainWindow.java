package edu.kit.iti.algover.gui;

import net.miginfocom.swing.MigLayout;

import javax.swing.*;
import java.awt.*;

/**
 * Create whole mainwindow
 * Created by sarah on 9/15/16.
 */
public final class MainWindow extends JFrame {

    //singleton object
    private static MainWindow instance = null;

    //GUICemter knows about top level GUI
    private static GUICenter center;


    //create the mainwindow with its panels
    public MainWindow(){
        this.center = new GUICenter(this);
        createMainWindow();

    }

    //singleton Mainwindow
    public static MainWindow getInstance(){
        if (instance == null) {
            instance = new MainWindow();
        }
        return instance;
    }

    //build the window
    public void createMainWindow() {


        MenuBar menuBar = new MenuBar(center);
        ToolBar toolbar = new ToolBar(center);

        JSplitPane splitPaneH = new JSplitPane(JSplitPane.HORIZONTAL_SPLIT);
       // splitPaneH.setResizeWeight(1.0);


        EditorPanel panel = new EditorPanel(center);
        //TreePanel tPanel = new TreePanel(center);
        ProjectBrowserPanel pPanel = new ProjectBrowserPanel(center);
        FooterPanel footerPanel = new FooterPanel(center);

        panel.add(footerPanel, BorderLayout.SOUTH);
        //splitPaneH.add(panel);
        //splitPaneH.add(pPanel);

        MigLayout migLayout = new MigLayout(
                "insets 0 0 0 0",       //Layout constraints
                "[grow]",               // Column constraints
                "[][][grow][]"          // Row constraints
        );

        this.setTitle("AlgoVer");
        this.setDefaultCloseOperation( JFrame.EXIT_ON_CLOSE );
        this.setBounds(250, 120, 300, 300);
        this.setLayout(migLayout);

        this.add(menuBar, "growx, wrap");
        this.add(toolbar, "growx, wrap");
        //this.add(splitPaneH, "grow, wrap");
        this.add(panel, "grow, wrap");
        this.add(footerPanel, "growx, wrap");

        this.setSize(500, 500);
        this.setVisible(true);


    }

     public GUICenter getCenter() {
        if (center == null) {
            throw new NullPointerException("KeYMediator is not set.");
        }
        return center;
    }


}
