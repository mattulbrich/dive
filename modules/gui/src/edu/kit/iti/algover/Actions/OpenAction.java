package edu.kit.iti.algover.Actions;





import edu.kit.iti.algover.gui.GUICenter;

import javax.swing.*;
import java.awt.*;
import java.awt.event.ActionEvent;
import java.awt.event.KeyEvent;
import java.io.File;

/**
 * Action that handles opening of a directory
 * Created by sarah on 9/14/16.
 */
public class OpenAction extends AbstractAction {
    GUICenter c;


    public OpenAction(GUICenter center){
        this.c = center;

        this.putValue(AbstractAction.NAME, "Open Project...");
        this.putValue(AbstractAction.ACCELERATOR_KEY, KeyStroke.getKeyStroke(KeyEvent.VK_O, KeyEvent.CTRL_MASK));
        this.putValue(AbstractAction.MNEMONIC_KEY, KeyEvent.VK_O);
    }

    @Override
    public void actionPerformed(ActionEvent e) {

        JFileChooser fc = new JFileChooser();
        fc.setFileSelectionMode(JFileChooser.DIRECTORIES_ONLY);
        int result = fc.showDialog(c.getMainwindow(), "Open Project Directory");

        if (result == JFileChooser.APPROVE_OPTION) {
            c.loadProject(fc.getSelectedFile());
           // c.setSelectedProjectDir(fc.getSelectedFile());
           // c.loadSelectedProject();
            System.out.println(fc.getSelectedFile());
            System.out.println("Open Action performed");
        }


    }

}
