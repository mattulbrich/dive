/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 *
 */

package edu.kit.iti.algover.swing.actions.nav;

import edu.kit.iti.algover.project.Project;
import edu.kit.iti.algover.proof.PVC;
import edu.kit.iti.algover.proof.PVCCollection;
import edu.kit.iti.algover.swing.DiveProperties;
import edu.kit.iti.algover.swing.actions.BarAction;
import edu.kit.iti.algover.swing.actions.BarManager.Initialisable;

import java.awt.event.ActionEvent;
import java.util.ArrayList;
import java.util.List;

public class ChangePVCAction extends BarAction implements Initialisable {

    private List<PVC> pvcList = new ArrayList<>();

    @Override
    public void initialised() {
        DiveProperties diveProp = getDiveCenter().properties();
        diveProp.project.addObserver(this::setProject);
        diveProp.activePVC.addObserver(this::checkEnabled);
        diveProp.noProjectMode.addObserver(this::checkEnabled);
        diveProp.onGoingProof.addObserver(this::checkEnabled);
    }

    private void checkEnabled() {
        DiveProperties diveProp = getDiveCenter().properties();
        PVC activePVC = diveProp.activePVC.getValue();
        if(diveProp.noProjectMode.getValue() == Boolean.TRUE ||
                diveProp.onGoingProof.getValue() == Boolean.TRUE) {
            setEnabled(false);
            return;
        }

        int index = pvcList.indexOf(activePVC);
        Object direction = getValue(EXTRA);
        if("next".equals(direction)) {
            if (index == pvcList.size() - 1) {
                setEnabled(false);
                return;
            }
        } else {
            if (index <= 0) {
                setEnabled(false);
                return;
            }
        }

        setEnabled(true);
    }

    private void setProject(Project project) {
        pvcList.clear();
        addToList(project.getAllPVCs());
    }

    private void addToList(PVCCollection coll) {
        if (coll.isPVCLeaf()) {
            pvcList.add(coll.getPVC());
        }
        coll.getChildren().forEach(this::addToList);
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        DiveProperties diveProp = getDiveCenter().properties();
        PVC activePVC = diveProp.activePVC.getValue();
        int index = pvcList.indexOf(activePVC);

        Object extra = getValue(EXTRA);
        if("next".equals(extra)) {
            index++;
        } else {
            index--;
        }

        diveProp.activePVC.setValue(pvcList.get(index));
    }
}
