package edu.kit.iti.algover.gui;

import edu.kit.iti.algover.gui.components.CustomProjectBrowser;
import edu.kit.iti.algover.model.ProjectTree;
import edu.kit.iti.algover.model.ProjectTreeBuilder;
import edu.kit.iti.algover.model.ProjectTreeModel;
import edu.kit.iti.algover.project.Project;
import edu.kit.iti.algover.project.ProjectBuilder;

import javax.swing.*;
import java.awt.*;
import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;
import java.io.File;

/**
 * Created by sarah on 9/16/16.
 */
public class ProjectBrowserPanel extends JPanel {
    String testDir = "modules/core/test-res/edu/kit/iti/algover/project";

    private GUICenter center;


    private JTree tree;

    public ProjectBrowserPanel(GUICenter center){
        this.center = center;


        //ProjectTreeBuilder pb = new ProjectTreeBuilder();
        //CustomProjectBrowser br = new CustomProjectBrowser(pb.buildProject(prepare()), center);
        this.setLayout(new BorderLayout());

        //this.add(br, BorderLayout.CENTER);
        center.addPropertyChangeListener(new MyPropertyChangeListener(center));

    }

    public Project prepare(){

        final File f1 = new File(testDir);

        ProjectBuilder pb = new ProjectBuilder();

        Project p = null;

        try {
            p = pb.buildProject(f1);
        } catch (Exception e) {
            e.printStackTrace();
        }
        return p;

    }

    private class MyPropertyChangeListener implements PropertyChangeListener {
        private final GUICenter center;

        public MyPropertyChangeListener(GUICenter center) {
            this.center = center;
        }

        @Override
        public void propertyChange(PropertyChangeEvent evt) {
            if(evt.getPropertyName() == GUICenter.PROJECT_LOADED){
                removeAll();
                ProjectTreeBuilder pb = new ProjectTreeBuilder();
                ProjectTree t = pb.buildProject(center.getLoadedProject());
                CustomProjectBrowser br = new CustomProjectBrowser(t, center);

                add(br, BorderLayout.CENTER);
                repaint();
                revalidate();

                center.setProjectTreeModel(t);
            }
        }
    }

}
