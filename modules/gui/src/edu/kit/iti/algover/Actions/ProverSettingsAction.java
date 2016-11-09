package edu.kit.iti.algover.Actions;

import edu.kit.iti.algover.gui.*;

import javax.swing.*;
import javax.swing.event.ListSelectionEvent;
import javax.swing.event.ListSelectionListener;
import java.awt.*;
import java.awt.event.ActionEvent;
import java.awt.event.KeyEvent;

/**
 * Created by Azadeh Shirvanian on 27.09.2016.
 */
public class ProverSettingsAction extends AbstractAction {

    GUICenter c;

    public ProverSettingsAction(GUICenter center){

        this.c = center;
        this.putValue(AbstractAction.NAME, "Settings...");
        this.putValue(AbstractAction.ACCELERATOR_KEY, KeyStroke.getKeyStroke(KeyEvent.VK_T, KeyEvent.CTRL_MASK));
        this.putValue(AbstractAction.MNEMONIC_KEY, KeyEvent.VK_S);
    }

    @Override
    public void actionPerformed(ActionEvent e) {

        SettingsWindow settingsWindow = new SettingsWindow(c);
        settingsWindow.setVisible(true);


        settingsWindow.getSettingsList().getSelectionModel().addListSelectionListener(new ListSelectionListener() {

            JPanel cards = settingsWindow.getCards();

            @Override
            public void valueChanged(ListSelectionEvent e) {

                CardLayout cl = (CardLayout)(cards.getLayout());

                if (settingsWindow.getSettingsList().getSelectedIndex() == 0)
                    cl.show(cards, "general");
                else if (settingsWindow.getSettingsList().getSelectedIndex() == 1)
                    cl.show(cards, "z3");
                else if (settingsWindow.getSettingsList().getSelectedIndex() == 2)
                    cl.show(cards, "dafny");
                else if (settingsWindow.getSettingsList().getSelectedIndex() == 3)
                    cl.show(cards, "key");

            }
        });

        //c.setSettingsWindow(settingsWindow);
    }
}
