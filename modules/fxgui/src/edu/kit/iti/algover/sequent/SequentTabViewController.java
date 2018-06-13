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
import java.util.List;

/**
 * Created by jklamroth on 6/7/18.
 */
public class SequentTabViewController {

    private TabPane view;
    private List<SequentController> controllers;
    private SequentActionListener listener;
    private ProofNodeSelector activeNode;
    private Proof activeProof;

    public SequentTabViewController(SequentActionListener listener) {
        this.listener = listener;
        view = new TabPane();
        controllers = new ArrayList<>();
        controllers.add(new SequentController(listener));
        view.getTabs().add(new Tab("default", controllers.get(0).getView()));
    }

    public void viewProofNode(ProofNodeSelector proofNodeSelector) {
        activeNode = proofNodeSelector;
        proofNodeSelector.optionalGet(controllers.get(view.getSelectionModel().getSelectedIndex()).getActiveProof()).ifPresent(proofNode -> {
            ProofRuleApplication pra = proofNode.getPsr();
            if(pra != null) {
                if (pra.getBranchCount() == controllers.size()) {
                    for (int i = 0; i < pra.getBranchCount(); ++i) {
                        controllers.get(i).setActiveNode(activeNode);
                        controllers.get(i).setActiveProof(activeProof);
                        controllers.get(i).viewProofNode(proofNodeSelector, i);
                        view.getTabs().get(i).setText(pra.getBranchInfo().get(i).getLabel());
                    }
                } else if (pra.getBranchCount() > controllers.size()) {
                    for (int i = 0; i < controllers.size(); ++i) {
                        controllers.get(i).setActiveNode(activeNode);
                        controllers.get(i).setActiveProof(activeProof);
                        controllers.get(i).viewProofNode(proofNodeSelector, i);
                        view.getTabs().get(i).setText(pra.getBranchInfo().get(i).getLabel());
                    }
                    for (int i = controllers.size(); i < pra.getBranchCount(); ++i) {
                        SequentController controller = new SequentController(listener);
                        controllers.add(controller);
                        view.getTabs().add(new Tab(pra.getBranchInfo().get(i).getLabel(), controller.getView()));
                        controllers.get(i).setActiveNode(activeNode);
                        controllers.get(i).setActiveProof(activeProof);
                        controllers.get(i).viewProofNode(proofNodeSelector, i);
                    }
                } else if (pra.getBranchCount() < controllers.size()) {
                    for (int i = 0; i < pra.getBranchCount(); ++i) {
                        controllers.get(i).setActiveNode(activeNode);
                        controllers.get(i).setActiveProof(activeProof);
                        controllers.get(i).resetProofApplicationPreview();
                        controllers.get(i).viewProofNode(proofNodeSelector, i);
                        view.getTabs().get(i).setText(pra.getBranchInfo().get(i).getLabel());
                    }
                    view.getTabs().remove(pra.getBranchCount(), controllers.size());
                    while (controllers.size() > pra.getBranchCount()) {
                        controllers.remove(controllers.size() - 1);
                    }
                }
                if(view.getTabs().size() == 1) {
                    view.getTabs().get(0).setText("default");
                }
            }
        });
    }

    public TabPane getView() {
        return view;
    }

    public void viewSequentForPVC(PVCEntity entity, Proof proof) {
        view.getTabs().clear();
        view.getTabs().add(new Tab("default", controllers.get(0).getView()));
        controllers.get(0).viewSequentForPVC(entity, proof);
        controllers.removeAll(controllers.subList(0, 0));
        activeNode = controllers.get(0).getActiveNodeSelector();
        activeProof = controllers.get(0).getActiveProof();
    }

    public SequentController getActiveSequentController() {
        return controllers.get(view.getSelectionModel().getSelectedIndex());
    }
}
