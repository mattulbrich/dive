package edu.kit.iti.algover.Actions;





import edu.kit.iti.algover.gui.GUICenter;

import javax.swing.*;
import java.awt.*;
import java.awt.event.ActionEvent;
import java.io.File;

/**
 * Action that handles opening of a directory
 * Created by sarah on 9/14/16.
 */
public class OpenAction extends AbstractAction {
    GUICenter c;


    public OpenAction(GUICenter center){
        this.c = center;
    }

    @Override
    public void actionPerformed(ActionEvent e) {

        JFileChooser fc = new JFileChooser();
        fc.setFileSelectionMode(JFileChooser.DIRECTORIES_ONLY);
        fc.showDialog(c.getMainwindow(), e.getActionCommand());
        System.out.println();
        c.setSelectedProjectDir(fc.getSelectedFile());
        c.loadSelectedProject();
        System.out.println(fc.getSelectedFile().getParent());
        System.out.println("Open Action performed");
    }


}
