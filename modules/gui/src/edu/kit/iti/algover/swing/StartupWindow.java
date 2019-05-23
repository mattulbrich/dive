/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 *
 */
package edu.kit.iti.algover.swing;

import java.awt.BorderLayout;
import java.awt.event.ActionEvent;
import java.io.IOException;
import java.net.URL;

import javax.swing.Action;
import javax.swing.Icon;
import javax.swing.JFrame;
import javax.swing.JLabel;

import edu.kit.iti.algover.swing.actions.BarAction;
import edu.kit.iti.algover.swing.actions.BarManager;
import edu.kit.iti.algover.swing.util.ExceptionDialog;
import edu.kit.iti.algover.swing.util.GUIUtil;

// TODO Documentation needed
public class StartupWindow extends JFrame {
    private static final long serialVersionUID = -250971288261688572L;

    private BarManager barManager;

    public StartupWindow() throws IOException {
        super("DIVE");
        makeGUI();
    }

    private void makeGUI() throws IOException {
        {
            URL resource = getClass().getResource("actions/menu.xml");
            if(resource == null) {
                throw new IOException("resource actions/menu.xml not found");
            }
            barManager = new BarManager(null, resource);
            barManager.putProperty(BarAction.PARENT_FRAME, this);
            setJMenuBar(barManager.makeMenubar("startup.menubar"));
        }
        getContentPane().add(new JLabel(makeImage()), BorderLayout.CENTER);
        setDefaultCloseOperation(EXIT_ON_CLOSE);
        pack();
    }

    private Icon makeImage() {
        return GUIUtil.makeIcon(getClass().getResource("img/logo.png"));
    }

    public void showSampleBrowser() {
        Action action = barManager.getAction("file.sampleBrowser");
        if(action == null) {
            ExceptionDialog.showExceptionDialog(this, "The sample browser cannot be initialised");
        } else {
            action.actionPerformed(new ActionEvent(this, 0, "commandline"));
        }
    }
}
