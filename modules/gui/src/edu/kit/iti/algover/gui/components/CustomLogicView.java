package edu.kit.iti.algover.gui.components;

import edu.kit.iti.algover.gui.GUICenter;
import edu.kit.iti.algover.gui.ProjectBrowserPanel;
import edu.kit.iti.algover.model.CustomLeaf;
import edu.kit.iti.algover.model.ProjectTree;
import edu.kit.iti.algover.proof.PVC;
import net.miginfocom.swing.MigLayout;

import javax.swing.*;
import java.awt.*;
import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;

/**
 * Created by sarah on 10/25/16.
 */
public class CustomLogicView extends JPanel{
     GUICenter center;
    JButton back = new JButton("Back to ProjectBrowser");
    public AssumptionField assumptions;
    MigLayout migLayout = new MigLayout(
                "insets 0 0 0 0",       //Layout constraints
                "[grow]",             // Column constraints
                "[0.3][grow]"          // Row constraints
        );
    public CustomLogicView(GUICenter center, PVC pvc) {
        System.out.println("Building CustomLogicView");
        this.center = center;

        this.setLayout(migLayout);
        this.setToolTipText("This is the logic view");

        //zwei große Felder
        this.setMinimumSize(super.getPreferredSize());

        this.setBorder(BorderFactory.createTitledBorder("Project "));
        this.center.addPropertyChangeListener( new MyPropertyChangeListener());

        back.addActionListener(e -> {
            if (e.getActionCommand().equals("Back to ProjectBrowser")) {
                CardLayout cl = (CardLayout) center.getMainwindow().getpPanel().cards.getLayout();
                cl.show(center.getMainwindow().getpPanel().cards, ProjectBrowserPanel.PR_BROWSER);
            }
        });
        this.add(back, "grow, wrap");

        assumptions = new AssumptionField(pvc);
        assumptions.setVisible(true);

        this.add(assumptions, "grow, wrap");
        //this.add(treetable, "grow, wrap");
        this.setVisible(true);
    }

    private class MyPropertyChangeListener implements PropertyChangeListener {
        @Override
        public void propertyChange(PropertyChangeEvent evt) {
            if(evt.getPropertyName().equals(GUICenter.PVC_FOR_DETAIL)){

                removeAll();
                assumptions = null;
                PVC pvc = center.getSelectedPVCForDetailView();
                assumptions = new AssumptionField(pvc);
                add(back, "grow, wrap");

                add(assumptions, "grow, wrap");
                setVisible(true);
            }
        }
    }

}
