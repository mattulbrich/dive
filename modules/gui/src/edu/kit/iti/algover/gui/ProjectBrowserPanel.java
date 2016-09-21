package edu.kit.iti.algover.gui;

import edu.kit.iti.algover.gui.components.CustomPVCBrowser;
import edu.kit.iti.algover.gui.components.CustomProjectBrowser;
import edu.kit.iti.algover.model.CustomLeaf;
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

    public static String PR_BROWSER = "Project Browser";
    public static String PVC_BROWSER = "PVC Browser";

    public CustomProjectBrowser br;
    public CustomPVCBrowser pvcbrowser;
    public JPanel cards;

    public ProjectBrowserPanel(GUICenter center){
        this.center = center;
        cards = new JPanel(new CardLayout());

        //ProjectTreeBuilder pb = new ProjectTreeBuilder();
        //CustomProjectBrowser br = new CustomProjectBrowser(pb.buildProject(prepare()), center);
        this.setLayout(new BorderLayout());
        this.add(cards, BorderLayout.CENTER);
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
                br = new CustomProjectBrowser(t, center);

                cards.add(br, PR_BROWSER);
                add(cards);
                //pvcbrowser = new CustomPVCBrowser(center, center.getSelectedProjectSubTree());
                //add(pvcbrowser, PVC_BROWSER);
                repaint();
                revalidate();

                center.setProjectTreeModel(t);
            }
            if(evt.getPropertyName() == GUICenter.TREE_SELECTION){
                if(center.getSelectedProjectSubTree() instanceof CustomLeaf){
                    pvcbrowser = new CustomPVCBrowser(center, center.getSelectedProjectSubTree());
                    cards.add(pvcbrowser, PVC_BROWSER);
                    CardLayout cl = (CardLayout)cards.getLayout();
                    cl.show(cards, PVC_BROWSER);
                }
            }
        }
    }

}
