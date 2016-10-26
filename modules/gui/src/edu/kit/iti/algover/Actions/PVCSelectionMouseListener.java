package edu.kit.iti.algover.Actions;

import edu.kit.iti.algover.gui.GUICenter;
import edu.kit.iti.algover.proof.PVC;
import edu.kit.iti.algover.proof.PVCCollection;
import edu.kit.iti.algover.proof.SinglePVC;
import org.jdesktop.swingx.JXTree;

import javax.swing.*;
import javax.swing.tree.TreePath;
import java.awt.event.MouseAdapter;
import java.awt.event.MouseEvent;
import java.awt.event.MouseListener;

/**
 * Created by sarah on 10/26/16.
 */
public class PVCSelectionMouseListener extends MouseAdapter {

    private final GUICenter center;
    private final JXTree tree;

    public PVCSelectionMouseListener(GUICenter center, JXTree tree) {
        this.tree = tree;
        this.center = center;
    }

    @Override
    public void mouseClicked(MouseEvent e) {

        if(e.getClickCount() == 1) {
//            TreePath path = treetable.getPathForLocation(e.getX(), e.getY());
//            ProjectTree lastPathComponent = (ProjectTree) path.getLastPathComponent();
//            center.setSelectedPath(path);
//
//            if(lastPathComponent.isLeaf()){
//                CustomLeaf l = (CustomLeaf) lastPathComponent;
//                center.setLoadedDafnySrc(l.getData().getFile().getAbsoluteFile());
//                center.setSelectedProjectSubTree(l);
//
//
//            }else{
//                center.setLoadedDafnySrc(lastPathComponent.path);
//                center.setSelectedProjectSubTree(lastPathComponent);
//
//            }
        }

        if(e.getClickCount() == 2) {
            TreePath path = tree.getPathForLocation(e.getX(), e.getY());

            PVCCollection lastPathComponent = null;
            if (path != null) {
                lastPathComponent = (PVCCollection) path.getLastPathComponent();
                if(lastPathComponent.isPVCLeaf() && !lastPathComponent.isEmptyPVC()){
                    SinglePVC sPVC =(SinglePVC) lastPathComponent;
                    PVC pvc = sPVC.getPVC();
                    center.setSelectedPVCForDetailView(pvc);

                }
            }


        }

    }
}
