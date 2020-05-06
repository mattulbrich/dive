/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.sequent;

import edu.kit.iti.algover.Lookup;
import edu.kit.iti.algover.browser.entities.PVCEntity;
import edu.kit.iti.algover.proof.Proof;
import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.proof.ProofNodeSelector;
import edu.kit.iti.algover.referenceHighlighting.ReferenceHighlightingHandler;
import edu.kit.iti.algover.referenceHighlighting.ReferenceHighlightingObject;
import edu.kit.iti.algover.references.ProofTermReferenceTarget;
import javafx.beans.value.ObservableValue;
import javafx.scene.control.Tab;
import javafx.scene.control.TabPane;

import java.util.*;
import java.util.stream.Collectors;

/**
 * Controller for the tabbed view containing tabs with sequent views controlled by {@link SequentController}
 * Created by jklamroth on 6/7/18.
 */
public class SequentTabViewController implements ReferenceHighlightingHandler {

    private TabPane view;
    private List<SequentController> controllers;
    private SequentActionListener listener;
    private ProofNodeSelector activeNode;
    private Proof activeProof;
    //The collection of prooftermrefs that should be highlighted
    private Set<ProofTermReferenceTarget> referenceTargetsToHighlight;
    private ProofTermReferenceTarget lastSelectedRefTarget;

    private Lookup lookup;


  /*  public void setReferenceTargetsToHighlight(Set<ProofTermReferenceTarget> referenceTargetsToHighlight) {
        //System.out.println("referenceTargetsToHighlight = " + referenceTargetsToHighlight);
        controllers.forEach(sequentController -> {
            sequentController.removeStyle("Target");
        });
        this.referenceTargetsToHighlight = referenceTargetsToHighlight;
    }*/



    public SequentTabViewController(SequentActionListener listener, Lookup lookup) {
        this.listener = listener;
        this.lookup = lookup;
        view = new TabPane();
        controllers = new ArrayList<>();
        controllers.add(new SequentController(listener, lookup));
        view.getTabs().add(new Tab("default", controllers.get(0).getView()));
        view.getSelectionModel().selectedIndexProperty().addListener(this::onTabSelected);
        referenceTargetsToHighlight = new HashSet<>();
        lastSelectedRefTarget = null;
        lookup.register(this, ReferenceHighlightingHandler.class);
        lookup.register(this, SequentTabViewController.class);

    }

    private List<ProofNodeSelector> getAllChildSelectors(ProofNodeSelector selector) {
        Optional<ProofNode> parentNode = selector.optionalGet(activeProof);
        if(!parentNode.isPresent()) {
            return new ArrayList<>();
        }
        int numChildren = parentNode.get().getSuccessors().size();
        List<ProofNodeSelector> res = new ArrayList<>();
        for(int i = 0; i < numChildren; ++i) {
            res.add(new ProofNodeSelector(selector, i));
        }
        return res;
    }


    public void viewProofNode(ProofNodeSelector proofNodeSelector) {


        ProofNodeSelector oldParentSelector = activeNode.getParentSelector();
        activeNode = proofNodeSelector;
        ProofNodeSelector parentSelector = activeNode.getParentSelector();
        if(parentSelector != null) {
            if(parentSelector.equals(oldParentSelector)) {
                view.getSelectionModel().select(activeNode.getPath()[activeNode.getPath().length - 1]);
                return;
            }
            List<ProofNodeSelector> children = getAllChildSelectors(parentSelector);
            if(children.size() == 0) {
                showProofNodes(Collections.singletonList(parentSelector));
            } else {
                showProofNodes(getAllChildSelectors(parentSelector));
            }
            view.getSelectionModel().select(activeNode.getPath()[activeNode.getPath().length - 1]);
        } else {
            showProofNodes(new ArrayList<>(Collections.singletonList(proofNodeSelector)));
        }

    }

    private void showProofNodes(List<ProofNodeSelector> proofNodeSelectors) {
        for(int i = 0; i < proofNodeSelectors.size(); ++i) {
            if(i >= view.getTabs().size()) {
                controllers.add(new SequentController(listener, lookup));
                view.getTabs().add(new Tab("default", controllers.get(i).getView()));
            }
            updateTab(proofNodeSelectors.get(i), i);
        }
        if(proofNodeSelectors.size() < view.getTabs().size()) {
            view.getTabs().remove(proofNodeSelectors.size(), view.getTabs().size());
            controllers = controllers.subList(0, proofNodeSelectors.size());
        }
    }

    private void updateTab(ProofNodeSelector selector, int idx) {
        Optional<ProofNode> opt = selector.optionalGet(activeProof);
        String name = "default";
        if(opt.isPresent() && opt.get().getLabel() != null && !opt.get().getLabel().equals("")) {
            name = opt.get().getLabel();
        }
        view.getTabs().get(idx).setText(name);
        Set<ProofTermReferenceTarget> collect = getReferenceTargetsToHighlight()
                .stream()
                .filter(proofTermReferenceTarget -> proofTermReferenceTarget.getProofNodeSelector().equals(selector))
                .collect(Collectors.toSet());
        controllers.get(idx).updateSequentController(selector, activeProof, collect);
       /* controllers.get(idx).setActiveNode(selector);
        controllers.get(idx).setActiveProof(activeProof);
        controllers.get(idx).viewProofNode(selector);*/
    }

    public TabPane getView() {
        return view;
    }

    public void viewSequentForPVC(PVCEntity entity, Proof proof) {
        if(controllers.size() == 0) {
            controllers.add(new SequentController(listener, lookup));
        } else {
            controllers.removeAll(controllers.subList(1, controllers.size()));
        }
        if(view.getTabs().size() == 0) {
            view.getTabs().add(new Tab("default", controllers.get(0).getView()));
        } else {
            view.getTabs().remove(1, view.getTabs().size());
        }

        controllers.get(0).forceViewSequentForPVC(entity, proof);
        activeNode = controllers.get(0).getActiveNodeSelector();
        activeProof = controllers.get(0).getActiveProof();
       // referenceGraph = controllers.get(0).getReferenceGraph();
    }

    public SequentController getActiveSequentController() {
        return controllers.get(view.getSelectionModel().getSelectedIndex());
    }

    private void onTabSelected(ObservableValue<? extends Number> observableValue, Number oldValue, Number newValue) {
        listener.onSwitchViewedNode(controllers.get(newValue.intValue()).getActiveNodeSelector());
    }

    public void viewReferences(Set<ProofTermReferenceTarget> proofTermReferenceTargetSet, ProofTermReferenceTarget selected){
        controllers.forEach(sequentController -> {
            sequentController.removeStyle("Target");
        });

        lastSelectedRefTarget = selected;
        this.referenceTargetsToHighlight = proofTermReferenceTargetSet;
        referenceTargetsToHighlight.add(lastSelectedRefTarget);


//        this.setReferenceTargetsToHighlight(proofTermReferenceTargetSet);
      /*  for(int i = 0; i< controllers.size(); i++){
            updateTab(controllers.get(i).getActiveNodeSelector(), i);
        }*/
    }

    @Override
    public void handleReferenceHighlighting(ReferenceHighlightingObject references) {
        viewReferences(references.getProofTermReferenceTargetSet(), references.getSelectedTarget());
    }

    @Override
    public void removeReferenceHighlighting() {
        referenceTargetsToHighlight.clear();
        controllers.forEach(sequentController -> {
            sequentController.removeStyle("Target");
        });
//        setReferenceTargetsToHighlight(referenceTargetsToHighlight);
    }

    public Set<ProofTermReferenceTarget> getReferenceTargetsToHighlight() {
        return referenceTargetsToHighlight;
    }

}