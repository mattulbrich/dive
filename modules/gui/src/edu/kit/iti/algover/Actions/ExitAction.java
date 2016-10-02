package edu.kit.iti.algover.Actions;

import edu.kit.iti.algover.gui.GUICenter;
import edu.kit.iti.algover.gui.MainWindow;

import javax.swing.*;
import java.awt.event.ActionEvent;
import java.awt.event.KeyEvent;

/**
 * Created by Azadeh Shirvanian on 21.09.2016.
 */
public class ExitAction extends AbstractAction {

    GUICenter c;
    int option;

    public ExitAction(GUICenter center){

        this.c = center;
        this.putValue(AbstractAction.NAME, "Exit");
        this.putValue(AbstractAction.ACCELERATOR_KEY, KeyStroke.getKeyStroke(KeyEvent.VK_Q, KeyEvent.CTRL_MASK));
        this.putValue(AbstractAction.MNEMONIC_KEY, KeyEvent.VK_E);

    }

    @Override
    public void actionPerformed(ActionEvent e) {

        this.option = JOptionPane.showConfirmDialog(MainWindow.getInstance(), "Are you sure you want to exit?", "Confirm Exit",
                JOptionPane.OK_CANCEL_OPTION, JOptionPane.QUESTION_MESSAGE);

        if (this.option == JOptionPane.OK_OPTION)
            System.exit(0);


    }
}
