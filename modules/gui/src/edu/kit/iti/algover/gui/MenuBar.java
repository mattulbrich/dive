package edu.kit.iti.algover.gui;

import edu.kit.iti.algover.Actions.*;

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
        //fileMenu.add(new OpenAction(center));
        JMenu projectMenu = new JMenu("Project");
        JMenu proverMenu = new JMenu("Prover");
        JMenu aboutMenu = new JMenu("About");
        JMenu helpMenu = new JMenu("Help");

        JMenuItem itemOpen = new JMenuItem("Open Project...");
        JMenuItem itemSave = new JMenuItem("Save Project...");
        JMenuItem itemExit = new JMenuItem("Exit");

        JMenu itemProveWith = new JMenu("Prove Whole Project With...");
        JMenuItem subItemAllProvers = new JMenuItem("All Provers");
        JMenuItem subItemZ3 = new JMenuItem("Z3");
        JMenuItem subItemDafny = new JMenuItem("Dafny");
        JMenuItem subItemKey = new JMenuItem("KeY");

        JMenuItem itemSettings = new JMenuItem("Settings...");

       // JMenuItem menuItemOpen = new JMenuItem();
      //  menuItemOpen.setAction(new OpenAction(center));
       // menuItemOpen.setText("Open...");

        itemProveWith.add(subItemAllProvers);
        itemProveWith.add(subItemZ3);
        itemProveWith.add(subItemDafny);
        itemProveWith.add(subItemKey);

        fileMenu.add(itemOpen);
        fileMenu.add(itemSave);
        fileMenu.add(itemExit);
        projectMenu.add(itemProveWith);
        proverMenu.add(itemSettings);

        this.add(fileMenu);
        this.add(projectMenu);
        this.add(proverMenu);
        this.add(aboutMenu);
        this.add(helpMenu);

        //Actions
        itemOpen.setAction(new OpenAction(center));
        itemSave.setAction(new SaveAction(center));
        itemExit.setAction(new ExitAction(center));
        subItemAllProvers.setAction(new ProveAllAction(center));
        subItemZ3.setAction(new ProveWithZ3Action(center));
        subItemDafny.setAction(new ProveWithDafnyAction(center));
        subItemKey.setAction(new ProveWithKeYAction(center));

    }
}
