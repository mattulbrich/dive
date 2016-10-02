package edu.kit.iti.algover.gui;

import edu.kit.iti.algover.Actions.*;

import javax.swing.*;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.awt.event.KeyEvent;

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

        JMenuItem itemHelp = new JMenuItem("Help");
        JMenuItem itemAbout = new JMenuItem(("About"));

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
        helpMenu.add(itemHelp);
        helpMenu.addSeparator();
        helpMenu.add(itemAbout);

        this.add(fileMenu);
        this.add(projectMenu);
        this.add(proverMenu);
        this.add(helpMenu);


        //Mnemonics and hotkeys
        fileMenu.setMnemonic(KeyEvent.VK_F);
        projectMenu.setMnemonic(KeyEvent.VK_P);
        proverMenu.setMnemonic(KeyEvent.VK_R);
        helpMenu.setMnemonic(KeyEvent.VK_H);
        itemProveWith.setMnemonic(KeyEvent.VK_P);
        itemHelp.setMnemonic(KeyEvent.VK_H);
        itemHelp.setAccelerator(KeyStroke.getKeyStroke(KeyEvent.VK_F1, 0));


        //Actions
        itemOpen.setAction(new OpenAction(center));
        itemSave.setAction(new SaveAction(center));
        itemExit.setAction(new ExitAction(center));
        subItemAllProvers.setAction(new ProveAllAction(center));
        subItemZ3.setAction(new ProveWithZ3Action(center));
        subItemDafny.setAction(new ProveWithDafnyAction(center));
        subItemKey.setAction(new ProveWithKeYAction(center));
        itemSettings.setAction(new ProverSettingsAction(center));
        itemAbout.setAction(new AboutAction(center));

    }
}
