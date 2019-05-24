/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 *
 */
package edu.kit.iti.algover.swing;

import java.awt.*;
import java.awt.event.WindowListener;
import java.io.IOException;
import java.net.URL;

import javax.swing.*;
import javax.swing.border.EtchedBorder;
import edu.kit.iti.algover.swing.actions.BarAction;
import edu.kit.iti.algover.swing.actions.BarManager;


/**
 * The class MainWindow describes the proof window for one single proof.
 *
 * The different views are layout using javadocking dockables allowing a very
 * flexible way to look at things.
 */
public class MainController {

    /*
     * 1) The JSplitPaneregisters some key strokes which are to used elsewhere.
     * We remove the according infos from the look and feel. The keys are then
     * available again.
     *
     * 2) Register a new docking model.
     *
     * 3) Replace the docking change executor to one which does not allow moving
     * panels to other windows (where they do not belong!)
     */
    static {
        UIManager.getDefaults().remove("SplitPane.ancestorInputMap");
        // DockingManager.setDockModel(new FloatDockModel());
        // DockingManager.setDockingExecutor(new SameFrameDockingExecutor());
    }

    /**
     * indicator for property changes on mainwindow that
     * window is initialised now.
     */
    // public static final String INITIALISED = "pseudo.initialised";

    private final DiveCenter diveCenter;
    private final String resourceName;

    private JFrame theFrame;

    // private SequentController sequentController;

    private PVCTreeController pvcTreeController;

    private DafnyCodeController dafnyCodeController;

    // private ScriptCodeController scriptCodeController;

    private BarManager barManager;

    private final int number;
    private static int counter = 0;
    private JPanel centerPane;
    private JLabel statusLine;

    /**
     * Instantiates a new main window.
     *
     * @param proofCenter the underlying proof center
     * @param resourceName the resource name to be used as title
     * @throws IOException if the barmanager fails to find needed resources
     */
    public MainController(DiveCenter diveCenter, String resourceName) throws IOException {
        this.diveCenter = diveCenter;
        this.resourceName = resourceName;
        this.number = ++counter;

        diveCenter.viewPort.addObserver(this::updateViewport);
    }

    private void updateViewport(Viewport newViewport) {
        JSplitPane sp = new JSplitPane();
        switch (newViewport) {
        case PVC_VIEW:
            sp.setLeftComponent(pvcTreeController.getComponent());
            sp.setRightComponent(dafnyCodeController.getComponent());
            sp.setDividerLocation(.2d);
            break;
        case CODE_VIEW:
            break;
        case PROOF_VIEW:
            break;
        default:
            throw new Error();
        }

        theFrame.getContentPane().add(sp, BorderLayout.CENTER);
    }

    void makeGUI() throws IOException {

        assert theFrame == null;
        theFrame = new JFrame("DIVE - " + resourceName);

        // setup the bar manager
        URL resource = getClass().getResource("actions/menu.xml");
        if(resource == null) {
            throw new IOException("resource actions/menu.xml not found");
        }

        barManager = new BarManager(null, resource);
        barManager.putProperty(BarAction.CENTER, diveCenter);
        barManager.putProperty(BarAction.PARENT_FRAME, theFrame);

        {
            this.pvcTreeController = new PVCTreeController(diveCenter);
            this.dafnyCodeController = new DafnyCodeController(diveCenter);
        }

        Container cp = theFrame.getContentPane();
        cp.setLayout(new BorderLayout());
        {
            JLabel toLeft = new JLabel("<<");
            cp.add(toLeft, BorderLayout.WEST);
        }
        {
            JLabel toRight = new JLabel(">>");
            cp.add(toRight, BorderLayout.EAST);
        }
        {
            centerPane = new JPanel();
            cp.add(centerPane, BorderLayout.CENTER);
        }
        {
            theFrame.setJMenuBar(barManager.makeMenubar("center.menubar"));
            cp.add(barManager.makeToolbar("center.toolbar"), BorderLayout.NORTH);
        }
        {
            statusLine = new JLabel("");
            statusLine.setBorder(BorderFactory.createEtchedBorder(EtchedBorder.LOWERED));
        }
        // ExitAction is actually also a WindowListener. ...
        // we call the bar manager so that no unnecessary copy
        // is created if it already exists.
//TODO        theFrame.addWindowListener((WindowListener) barManager.makeAction("general.close"));
        theFrame.setDefaultCloseOperation(WindowConstants.DO_NOTHING_ON_CLOSE);
        theFrame.setSize(1000, 700);
    }



    public void dispose() {
        theFrame.dispose();
    }

    public BarManager getBarManager() {
        return barManager;
    }

    public JFrame getFrame() {
        return theFrame;
    }
}