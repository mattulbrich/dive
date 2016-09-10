package edu.kit.iti.algover.gui;

import javax.swing.*;

/**
 * The menu bar.
 *
 * Created by sony on 06.09.2016.
 */

public class MenuBar extends JMenuBar
{
    JMenu fileMenu = new JMenu("File");
    JMenu editMenu = new JMenu("Edit");

    JMenuItem menuItemOpen = new JMenuItem("Open...");
    JMenuItem menuItemSave = new JMenuItem("Save...");

    public MenuBar()
    {
        add(fileMenu);
        add(editMenu);

        fileMenu.add(menuItemOpen);
        fileMenu.add(menuItemSave);
    }
}
