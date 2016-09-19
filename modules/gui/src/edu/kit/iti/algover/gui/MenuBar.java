package edu.kit.iti.algover.gui;

import edu.kit.iti.algover.Actions.OpenAction;

import javax.swing.*;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;

/**
 * The menu bar.
 *
 * Created by sony on 06.09.2016.
 */

public class MenuBar extends JMenuBar
{
    GUICenter center;






    public MenuBar(GUICenter center)
    {
        this.center = center;
        createMenuBar();
    }

    private void createMenuBar() {

        JMenu fileMenu = new JMenu("File");
        fileMenu.add(new OpenAction(center));
        JMenu editMenu = new JMenu("Edit");


        JMenuItem menuItemSave = new JMenuItem("Save...");
       // JMenuItem menuItemOpen = new JMenuItem();
      //  menuItemOpen.setAction(new OpenAction(center));
       // menuItemOpen.setText("Open...");

     //   fileMenu.add(menuItemOpen);
        fileMenu.add(menuItemSave);

        add(fileMenu);
        add(editMenu);


    }
}
