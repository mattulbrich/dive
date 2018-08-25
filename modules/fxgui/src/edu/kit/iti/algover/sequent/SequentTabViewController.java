package edu.kit.iti.algover.sequent;

import edu.kit.iti.algover.browser.entities.PVCEntity;
import edu.kit.iti.algover.proof.Proof;
import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.proof.ProofNodeSelector;
import edu.kit.iti.algover.references.ReferenceGraph;
import edu.kit.iti.algover.rules.BranchInfo;
import edu.kit.iti.algover.rules.ProofRuleApplication;
import javafx.scene.control.Tab;
import javafx.scene.control.TabPane;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Optional;

/**
 * Created by jklamroth on 6/7/18.
 */
public class SequentTabViewController {

    private TabPane view;
    private List<SequentController> controllers;
    private SequentActionListener listener;
    private ProofNodeSelector activeNode;
    private Proof activeProof;
    private ReferenceGraph referenceGraph;

    public SequentTabViewController(SequentActionListener listener) {
        this.listener = listener;
        view = new TabPane();
        controllers = new ArrayList<>();
        controllers.add(new SequentController(listener));
        view.getTabs().add(new Tab("default", controllers.get(0).getView()));
    }

    private List<ProofNodeSelector> getAllChildSelectors(ProofNodeSelector selector) {
        Optional<ProofNode> parentNode = selector.optionalGet(activeProof);
        if(!parentNode.isPresent()) {
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
        for(SequentController controller : controllers) {
            controller.updateReferenceGraph(referenceGraph);
        }
    }

    private void showProofNodes(List<ProofNodeSelector> proofNodeSelectors) {
        for(int i = 0; i < proofNodeSelectors.size(); ++i) {
            if(i >= view.getTabs().size()) {
                controllers.add(new SequentController(listener));
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
        if(opt.isPresent() && opt.get().getLabel() != null) {
            name = opt.get().getLabel();
        }
        view.getTabs().get(idx).setText(name);
        controllers.get(0).setActiveNode(selector);
        controllers.get(0).setActiveProof(activeProof);
        controllers.get(0).viewProofNode(selector);
    }

    public TabPane getView() {
        return view;
    }

    public void viewSequentForPVC(PVCEntity entity, Proof proof) {
        if(controllers.size() == 0) {
            controllers.add(new SequentController(listener));
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
        referenceGraph = controllers.get(0).getReferenceGraph();
    }

    public SequentController getActiveSequentController() {
        return controllers.get(view.getSelectionModel().getSelectedIndex());
    }
}
