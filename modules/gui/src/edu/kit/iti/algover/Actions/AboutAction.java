package edu.kit.iti.algover.Actions;

import edu.kit.iti.algover.gui.GUICenter;
import edu.kit.iti.algover.gui.MainWindow;

import javax.swing.*;
import java.awt.event.ActionEvent;

/**
 * Created by Azadeh Shirvanian on 26.09.2016.
 */
public class AboutAction extends AbstractAction {

    GUICenter c;
    String aboutText = "<html><h3>AlgoVer</h3>" +
            "<br>bla <i>bla</i> <span style='color:green'>bla</span></html>";

    public AboutAction(GUICenter center) {

        this.c = center;
        this.putValue(AbstractAction.NAME, "About");

    }

    @Override
    public void actionPerformed(ActionEvent e) {

        JOptionPane.showMessageDialog(MainWindow.getInstance(), aboutText, "About AlgoVer", JOptionPane.INFORMATION_MESSAGE);

    }
}
