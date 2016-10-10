package edu.kit.iti.algover.gui;

import net.miginfocom.swing.MigLayout;
import sun.management.snmp.jvmmib.EnumJvmClassesVerboseLevel;

import javax.swing.*;
import java.awt.*;

/**
 * Footer panel contains two labels at right and left.
 *
 * Created by Azadeh Shirvanian on 13.09.2016.
 */
public class EditorFooterPanel extends JPanel {

    JLabel leftLabel;

    public JLabel getRightLabel() {
        return rightLabel;
    }

    public void setRightLabelText(String text) {
        this.rightLabel.setText(text);
    }

    JLabel rightLabel = new JLabel("Line");

    MigLayout migLayout = new MigLayout(
            "insets 0 5 0 5",       //Layout constraints
            "[grow][grow]",               // Column constraints
            ""          // Row constraints
    );

    public EditorFooterPanel(GUICenter center){
        leftLabel = new JLabel("Left");
        setLayout(migLayout);

        add(leftLabel, "align left");
        add(rightLabel, "align right");
    }
}
