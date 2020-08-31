/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.sequent;

import edu.kit.iti.algover.Lookup;
import edu.kit.iti.algover.PropertyManager;
import edu.kit.iti.algover.proof.PVC;
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
    private List<ProofNodeSelector> displayedNodes = new ArrayList<>();
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



    public SequentTabViewController(Lookup lookup) {
        this.lookup = lookup;
        view = new TabPane();
        controllers = new ArrayList<>();
        controllers.add(new SequentController());
        view.getTabs().add(new Tab("default", controllers.get(0).getView()));
        view.getSelectionModel().selectedIndexProperty().addListener(this::onTabSelected);
        view.setTabClosingPolicy(TabPane.TabClosingPolicy.UNAVAILABLE);
        referenceTargetsToHighlight = new HashSet<>();
        lastSelectedRefTarget = null;
        lookup.register(this, ReferenceHighlightingHandler.class);
        lookup.register(this, SequentTabViewController.class);

        PropertyManager.getInstance().currentProofNodeSelector.addListener(((observable, oldValue, newValue) -> {
            if (newValue != null) {
                this.viewProofNode(newValue);
            }
        }));
        PropertyManager.getInstance().currentPVC.addListener(((observable, oldValue, newValue) -> {
            if(newValue == null) {
                getActiveSequentController().clear();
            }
        }));
        PropertyManager.getInstance().currentFile.addListener(((observable, oldValue, newValue) -> {
            if(newValue == null) {
                getActiveSequentController().clear();
            }
        }));
        PropertyManager.getInstance().currentPVC.addListener(((observable, oldValue, newValue) -> this.viewSequentForPVC(
                newValue,
                PropertyManager.getInstance().currentProof.get()
        )));
    }

    private List<ProofNodeSelector> getAllChildSelectors(ProofNodeSelector selector) {
        Optional<ProofNode> parentNode = selector.optionalGet(PropertyManager.getInstance().currentProof.get());
        if(parentNode.isEmpty()) {
            return new ArrayList<>();
        }
        int numChildren = parentNode.get().getChildren().size();
        List<ProofNodeSelector> res = new ArrayList<>();
        for(int i = 0; i < numChildren; ++i) {
            res.add(new ProofNodeSelector(selector, i));
        }
        return res;
    }


    public void viewProofNode(ProofNodeSelector proofNodeSelector) {
        if(proofNodeSelector != null) {
            ProofNodeSelector parentSelector = proofNodeSelector.getParentSelector();
            if (parentSelector != null) {
                if (displayedNodes.contains(proofNodeSelector)) {
                    view.getSelectionModel().select(displayedNodes.indexOf(proofNodeSelector));
                    return;
                }
                List<ProofNodeSelector> children = getAllChildSelectors(parentSelector);
                showProofNodes(children);
                view.getSelectionModel().select(proofNodeSelector.getPath()[proofNodeSelector.getPath().length - 1]);
                displayedNodes = children;
            } else {
                List<ProofNodeSelector> l = Collections.singletonList(proofNodeSelector);
                showProofNodes(l);
                displayedNodes = l;
            }
            PropertyManager.getInstance().currentProofNodeSelector.set(proofNodeSelector);
        }
    }

    private void showProofNodes(List<ProofNodeSelector> proofNodeSelectors) {
        for(int i = 0; i < proofNodeSelectors.size(); ++i) {
            if(i >= view.getTabs().size()) {
                controllers.add(new SequentController());
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
        Optional<ProofNode> opt = selector.optionalGet(PropertyManager.getInstance().currentProof.get());
        String name = "default";
        if(opt.isPresent() && opt.get().getLabel() != null && !opt.get().getLabel().equals("")) {
            name = opt.get().getLabel();
        }
        view.getTabs().get(idx).setText(name);
        Set<ProofTermReferenceTarget> collect = getReferenceTargetsToHighlight()
                .stream()
                .filter(proofTermReferenceTarget -> proofTermReferenceTarget.getProofNodeSelector().equals(selector))
                .collect(Collectors.toSet());
        controllers.get(idx).updateSequentController(selector, collect);
       /* controllers.get(idx).setActiveNode(selector);
        controllers.get(idx).viewProofNode(selector);*/
    }

    public TabPane getView() {
        return view;
    }

    public void viewSequentForPVC(PVC pvc, Proof proof) {
        if(pvc != null && proof != null) {
            if (controllers.size() == 0) {
                controllers.add(new SequentController());
            } else {
                controllers.removeAll(controllers.subList(1, controllers.size()));
            }
            if (view.getTabs().size() == 0) {
                view.getTabs().add(new Tab("default", controllers.get(0).getView()));
            } else {
                view.getTabs().remove(1, view.getTabs().size());
            }

            controllers.get(0).viewSequentForPVC(pvc, proof);
            PropertyManager.getInstance().currentProofNodeSelector.set(controllers.get(0).getActiveNodeSelector());
            // referenceGraph = controllers.get(0).getReferenceGraph();
        }
    }

    public SequentController getActiveSequentController() {
        return controllers.get(view.getSelectionModel().getSelectedIndex());
    }

    private void onTabSelected(ObservableValue<? extends Number> observableValue, Number oldValue, Number newValue) {
        PropertyManager.getInstance().currentProofNodeSelector.set(controllers.get(newValue.intValue()).getActiveNodeSelector());
    }

    public void viewReferences(Set<ProofTermReferenceTarget> proofTermReferenceTargetSet, ProofTermReferenceTarget selected){
        controllers.forEach(sequentController -> sequentController.removeStyle("Target"));

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
        controllers.forEach(sequentController -> sequentController.removeStyle("Target"));
//        setReferenceTargetsToHighlight(referenceTargetsToHighlight);
    }

    public Set<ProofTermReferenceTarget> getReferenceTargetsToHighlight() {
        return referenceTargetsToHighlight;
    }

}