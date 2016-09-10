package edu.kit.iti.algover.gui;

import javax.swing.*;
import java.awt.*;

/**
 * EditorPanel contains a tabbed pane.
 *
 * Created by sony on 07.09.2016.
 */

public class EditorPanel extends JPanel{

    TabbedPane tabbedPane = new TabbedPane();

    public EditorPanel()
    {
        setLayout(new BorderLayout());
        add(tabbedPane, BorderLayout.CENTER);
    }
}
