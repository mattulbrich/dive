package edu.kit.iti.algover.gui;

import edu.kit.iti.algover.gui.components.CustomPVCBrowser;
import edu.kit.iti.algover.gui.components.CustomProjectBrowser;
import edu.kit.iti.algover.model.ProjectTree;
import edu.kit.iti.algover.model.ProjectTreeBuilder;
import net.miginfocom.swing.MigLayout;

import javax.swing.*;
import java.awt.*;
import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;

/**
 * Create whole mainwindow
 * Created by sarah on 9/15/16.
 */
public final class MainWindow extends JFrame {

    //return panel with editortabbedpane and footer
    public EditorPanel getEditorPanel() {
        return panel;
    }

    private EditorPanel panel;
    //singleton object
    private static MainWindow instance = null;

    //GUICemter knows about top level GUI
    private static GUICenter center;

    private SettingsWindow settingsWindow;


    public ProjectBrowserPanel getpPanel() {
        return pPanel;
    }

    private ProjectBrowserPanel pPanel;
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
        splitPaneH.setResizeWeight(0.7);
        //JPanel rightSide = new JPanel(new CardLayout());

        panel = new EditorPanel(center);
        //TreePanel tPanel = new TreePanel(center);
        //EditorFooterPanel editorFooterPanel = new EditorFooterPanel(center);
        //panel.add(editorFooterPanel, BorderLayout.SOUTH);


        pPanel = new ProjectBrowserPanel(center);

        splitPaneH.add(panel);
        //splitPaneH.add(rightSide);
        splitPaneH.add(pPanel);




        MigLayout migLayout = new MigLayout(
                "insets 0 0 0 0",       //Layout constraints
                "[grow]",               // Column constraints
                "[][][grow][]"          // Row constraints
        );

        this.setTitle("AlgoVer");
        this.setDefaultCloseOperation( JFrame.EXIT_ON_CLOSE );
        //this.setBounds(250, 120, 300, 300);
        this.setLayout(migLayout);

        this.add(menuBar, "growx, wrap");
        this.add(toolbar, "growx, wrap");
        this.add(splitPaneH, "grow, wrap");

        //this.add(panel, "grow, wrap");
        //this.add(footerPanel, "growx, wrap");

        this.setSize(850, 850);
        this.setExtendedState(JFrame.MAXIMIZED_BOTH);

        this.setVisible(true);


    }

     public GUICenter getCenter() {
        if (center == null) {
            throw new NullPointerException("GUICenter is not set.");
        }
        return center;
    }

    public SettingsWindow getSettingsWindow() {
        //System.out.println("getterSW");
        return settingsWindow;
    }

    public void setSettingsWindow(SettingsWindow settingsWindow)
    {
        //System.out.println("setterSW");
        this.settingsWindow = settingsWindow;
    }

}
