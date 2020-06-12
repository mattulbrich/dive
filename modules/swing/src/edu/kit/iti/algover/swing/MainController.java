/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 *
 */
package edu.kit.iti.algover.swing;

import java.awt.*;
import java.awt.event.MouseAdapter;
import java.awt.event.MouseEvent;
import java.awt.event.WindowListener;
import java.io.IOException;
import java.net.URL;
import java.util.EnumMap;
import java.util.Map;

import javax.swing.*;
import javax.swing.border.EtchedBorder;
import edu.kit.iti.algover.swing.actions.BarAction;
import edu.kit.iti.algover.swing.actions.BarManager;
import edu.kit.iti.algover.swing.browser.PVCBrowserController;
import edu.kit.iti.algover.swing.code.DafnyCodeController;
import edu.kit.iti.algover.swing.rules.RuleBayController;
import edu.kit.iti.algover.swing.script.ScriptCodeController;
import edu.kit.iti.algover.swing.sequent.SequentController;
import edu.kit.iti.algover.swing.util.GUIUtil;
import edu.kit.iti.algover.swing.util.Log;
import edu.kit.iti.algover.util.ExceptionDetails;


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

    public static Image WINDOW_ICON = loadLogoIcon();

    /**
     * indicator for property changes on mainwindow that
     * window is initialised now.
     */
    // public static final String INITIALISED = "pseudo.initialised";

    private final DiveCenter diveCenter;

    private final String resourceName;
    private JFrame theFrame;

    private SequentController sequentController;

    private PVCBrowserController pvcTreeController;

    private DafnyCodeController dafnyCodeController;
    private ScriptCodeController scriptCodeController;
    private RuleBayController ruleBayController;
    private Map<Viewport, Integer> separatorPositions =
            new EnumMap<>(Viewport.class);

    private BarManager barManager;

    private final int number;

    private static int counter = 0;
    private JSplitPane centerPane;
    private JLabel statusLine;
    private JLabel toLeftControl;
    private JLabel toRightControl;
    private Container mainPane;
    private String title;
    private JSplitPane scriptAndRuleComponent;

    /**
     * Instantiates a new main window.
     *
     * @param resourceName the resource name to be used as title
     * @throws IOException if the barmanager fails to find needed resources
     */
    public MainController(DiveCenter diveCenter, String resourceName) throws IOException {
        this.diveCenter = diveCenter;
        this.resourceName = resourceName;
        this.number = ++counter;

        separatorPositions.put(Viewport.PVC_VIEW, 200);
        separatorPositions.put(Viewport.CODE_VIEW, 500);
        separatorPositions.put(Viewport.PROOF_VIEW, 500);

        diveCenter.properties().viewPort.addObserver(this::updateViewport);
        diveCenter.properties().terminated.addObserver(this::dispose);
        diveCenter.properties().unsavedChanges.addObserver(this::updateTitle);
    }

    private void updateTitle(boolean unsavedChanges) {
        if(unsavedChanges) {
            theFrame.setTitle(title + " *");
        } else {
            theFrame.setTitle(title);
        }
    }

    private void updateViewport(Viewport oldViewPort, Viewport newViewport) {
        Log.log(Log.VERBOSE, "Switching to viewport " + newViewport);
        if (oldViewPort != null && centerPane != null) {
            separatorPositions.put(oldViewPort, centerPane.getDividerLocation());
            mainPane.remove(centerPane);
        }

        centerPane = new JSplitPane(JSplitPane.HORIZONTAL_SPLIT);
        mainPane.add(centerPane, BorderLayout.CENTER);

        switch (newViewport) {
        case PVC_VIEW:
            centerPane.setLeftComponent(pvcTreeController.getComponent());
            centerPane.setRightComponent(dafnyCodeController.getComponent());
            toLeftControl.setEnabled(false);
            toRightControl.setEnabled(true);
            break;
        case CODE_VIEW:
            centerPane.setLeftComponent(dafnyCodeController.getComponent());
            centerPane.setRightComponent(sequentController.getComponent());
            toLeftControl.setEnabled(true);
            toRightControl.setEnabled(true);
            break;
        case PROOF_VIEW:
            centerPane.setLeftComponent(sequentController.getComponent());
            centerPane.setRightComponent(scriptAndRuleComponent);
            toLeftControl.setEnabled(true);
            toRightControl.setEnabled(false);
            break;
        default:
            throw new Error();
        }

        Integer newPos = separatorPositions.get(newViewport);
        centerPane.setDividerLocation(newPos);

        theFrame.revalidate();

    }

    void makeGUI() throws IOException {

        assert theFrame == null;
        this.title = "DIVE - " + resourceName;
        theFrame = new JFrame(title);

        // setup the bar manager
        URL resource = getClass().getResource("actions/menu.xml");
        if(resource == null) {
            throw new IOException("resource actions/menu.xml not found");
        }

        barManager = new BarManager(null, resource);
        barManager.putProperty(BarAction.CENTER, diveCenter);
        barManager.putProperty(BarAction.PARENT_FRAME, theFrame);

        {
            this.pvcTreeController = new PVCBrowserController(diveCenter);
            this.dafnyCodeController = new DafnyCodeController(diveCenter);
            this.sequentController = new SequentController(diveCenter);
            this.scriptCodeController = new ScriptCodeController(diveCenter);
            this.ruleBayController = new RuleBayController(diveCenter);
        }

        Container cp = theFrame.getContentPane();
        cp.setLayout(new BorderLayout());
        {
            toLeftControl = new JLabel(" \u25c0 ");
            toLeftControl.addMouseListener(new MouseAdapter() {
                @Override
                public void mouseClicked(MouseEvent e) {
                    if (SwingUtilities.isLeftMouseButton(e) && e.getClickCount() == 1) {
                        diveCenter.moveViewport(-1);
                    }
                }
            });
            toLeftControl.setFont(toLeftControl.getFont().deriveFont(20f));
            cp.add(toLeftControl, BorderLayout.WEST);
        }
        {
            toRightControl = new JLabel(" \u25b6 ");
            toRightControl.addMouseListener(new MouseAdapter() {
                @Override
                public void mouseClicked(MouseEvent e) {
                    if (SwingUtilities.isLeftMouseButton(e) && e.getClickCount() == 1) {
                        diveCenter.moveViewport(+1);
                    }
                }
            });
            toRightControl.setFont(toRightControl.getFont().deriveFont(20f));
            cp.add(toRightControl, BorderLayout.EAST);
        }
        {
            scriptAndRuleComponent = new JSplitPane(JSplitPane.VERTICAL_SPLIT);
            scriptAndRuleComponent.setTopComponent(scriptCodeController.getComponent());
            scriptAndRuleComponent.setBottomComponent(ruleBayController.getComponent());
            scriptAndRuleComponent.setDividerLocation(300);
        }
        {
            // there used to be another panel here.
            mainPane = cp;
            centerPane = new JSplitPane(JSplitPane.HORIZONTAL_SPLIT);
            mainPane.add(centerPane, BorderLayout.CENTER);
        }
        {
            theFrame.setJMenuBar(barManager.makeMenubar("center.menubar"));
            cp.add(barManager.makeToolbar("center.toolbar"), BorderLayout.NORTH);
        }
        {
            statusLine = new JLabel("this is difficult");
            statusLine.setFont(UIManager.getFont("TextArea.font"));
            statusLine.setBorder(BorderFactory.createEtchedBorder(EtchedBorder.LOWERED));
            cp.add(statusLine, BorderLayout.SOUTH);
        }
        // ExitAction is actually also a WindowListener. ...
        // we call the bar manager so that no unnecessary copy is created
        theFrame.addWindowListener((WindowListener) barManager.makeAction("general.close"));
        theFrame.setDefaultCloseOperation(WindowConstants.DO_NOTHING_ON_CLOSE);
        theFrame.setSize(1000, 700);
        theFrame.setIconImage(WINDOW_ICON);
    }

    public void dispose() {
        theFrame.setVisible(false);
        theFrame.dispose();
    }

    public BarManager getBarManager() {
        return barManager;
    }

    public JFrame getFrame() {
        return theFrame;
    }

    public ScriptCodeController getScriptCodeController() {
        return scriptCodeController;
    }

    public DafnyCodeController getDafnyCodeController() {
        return dafnyCodeController;
    }

    public void setStatus(String string) {
        statusLine.setText(string);
        statusLine.setToolTipText("");
        statusLine.setForeground(Color.black);
    }

    public void setStatus(Exception e) {
        CharSequence niceMsg = ExceptionDetails.getNiceErrorMessage(e);
        statusLine.setToolTipText("<html><pre>" + niceMsg + "</pre>");
        statusLine.setForeground(Color.red);
        String msg = e.getMessage();
        if(msg == null) {
            msg = e.getClass().getSimpleName() + " with no message. 'Something went wrong somewhere.'";
            Log.log(Log.DEBUG, "There is an exception without message. That should be fixed.");
            Log.stacktrace(Log.DEBUG, e);
        }
        statusLine.setText(msg);
    }

    private static Image loadLogoIcon() {
        return ((ImageIcon)GUIUtil.makeIcon(MainController.class.getResource("img/icon.png"))).getImage();
    }
}