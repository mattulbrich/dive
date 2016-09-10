package edu.kit.iti.algover.gui;

import javax.swing.*;

/**
 * TabbedPane consists of a text area inside a scroll pane.
 *
 * Created by sony on 07.09.2016.
 */

public class TabbedPane extends JTabbedPane {

    JTextArea tx = new JTextArea();
    JScrollPane sc = new JScrollPane(tx);

    public TabbedPane() {
        add(sc);
    }
}
