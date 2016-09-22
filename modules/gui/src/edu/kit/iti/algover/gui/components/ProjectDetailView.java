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

    MigLayout migLayout = new MigLayout(
            "insets 10 10 10 10",       //Layout constraints
            "[grow]",             // Column constraints
            "[grow][grow 0.2]"          // Row constraints
    );
    public ProjectDetailView(GUICenter center, JPanel p)
    {
        this.setLayout(migLayout);
        this.add(new Label("Details"), "grow, wrap");
        this.parent = p;
        this.center = center;
        this.center.addPropertyChangeListener(new MyPropertyChangeListener());
        this.table = makeTable();


        JScrollPane pane = new JScrollPane(table);
        //pane.add(this.table);
        this.add(pane, "grow, wrap");

    }

    private JTable makeTable() {
        Object[] cols= {"Category", "Details"};
        JTable table = new JTable();
        table.setModel(new SubtreeTableModel(selected));
        //table.setPreferredSize(new Dimension(200, 200));
        table.setTableHeader(null);
        return table;
    }


    private void showDetails(ProjectTree selected) {
        removeAll();
        add(new Label("Details"), "grow, wrap");
        table.setModel(new SubtreeTableModel(selected));
        JScrollPane pane = new JScrollPane(table);
       // pane.add(table);
        add(pane, "grow, wrap");


    }


    private class MyPropertyChangeListener implements PropertyChangeListener {
        @Override
        public void propertyChange(PropertyChangeEvent evt) {
            if(evt.getPropertyName().equals(GUICenter.SUBTREE_SELECTION)){

                if(evt.getNewValue() instanceof ProjectTree) {
                    selected = (ProjectTree) evt.getNewValue();
                    if (selected.name != "Project"){
                        removeAll();
                        showDetails(selected);
                        validate();
                        repaint();
                    }

                }
            }
        }
    }
}
