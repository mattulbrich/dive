package edu.kit.iti.algover.gui.components;

import edu.kit.iti.algover.gui.GUICenter;
import edu.kit.iti.algover.model.CustomLeaf;
import edu.kit.iti.algover.model.ProjectTree;
import edu.kit.iti.algover.model.SubtreeTableModel;
import net.miginfocom.swing.MigLayout;

import javax.swing.*;
import javax.swing.table.DefaultTableModel;
import javax.swing.table.TableColumn;
import java.awt.*;
import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;

/**
 * This component will be used to show details of project components such as their parent class/project, their status etc.
 * Created by sarah on 9/19/16.
 */
public class ProjectDetailView extends JPanel {
    GUICenter center;

    ProjectTree selected;

    JPanel parent;

    JTable table;
    public ProjectDetailView(GUICenter center, JPanel p)
    {
        this.setLayout(new MigLayout());
        this.add(new Label("Details"), "grow, wrap");
        this.parent = p;
        this.center = center;
        this.center.addPropertyChangeListener(new MyPropertyChangeListener());
        this.table = makeTable();

        JPanel tPanel = new JPanel(new BorderLayout());
        tPanel.add(this.table, BorderLayout.CENTER);
        this.add(tPanel, "grow, wrap");

    }

    private JTable makeTable() {
        Object[] cols= {"Category", "Details"};
        JTable table = new JTable();
        table.setModel(new SubtreeTableModel(selected));

        return table;
    }


    private void showDetails(ProjectTree selected) {
        removeAll();
        table.setModel(new SubtreeTableModel(selected));
        revalidate();
        parent.repaint();

    }


    private class MyPropertyChangeListener implements PropertyChangeListener {
        @Override
        public void propertyChange(PropertyChangeEvent evt) {
            if(evt.getPropertyName().equals(GUICenter.TREE_SELECTION)){
                removeAll();
                if(evt.getNewValue() instanceof ProjectTree){
                    selected = (ProjectTree) evt.getNewValue();

                    showDetails(selected);
                    validate();
                    repaint();
                   // System.out.println(selected.getDetails()[1][1]);

                }
            }
        }
    }
}
