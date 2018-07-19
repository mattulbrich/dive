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

    public SequentTabViewController(SequentActionListener listener) {
        this.listener = listener;
        view = new TabPane();
        controllers = new ArrayList<>();
        controllers.add(new SequentController(listener));
        view.getTabs().add(new Tab("default", controllers.get(0).getView()));
    }

    public void viewProofNode(ProofNodeSelector proofNodeSelector) {
        ProofNodeSelector oldParentSelector = activeNode.getParentSelector();
        activeNode = proofNodeSelector;
        ProofNodeSelector parentSelector = activeNode.getParentSelector();
        int numChildren;
        if(parentSelector != null) {
            if(parentSelector.equals(oldParentSelector)) {
                view.getSelectionModel().select(activeNode.getPath()[activeNode.getPath().length - 1]);
                return;
            }
            Optional<ProofNode> parentNode = parentSelector.optionalGet(activeProof);
            if(parentNode.isPresent()) {
                numChildren = parentNode.get().getChildren().size();
            } else {
                numChildren = 1;
            }
            if (numChildren == controllers.size()) {
                for (int i = 0; i < numChildren; ++i) {
                    ProofNodeSelector ithNode = new ProofNodeSelector(parentSelector, i);
                    controllers.get(i).setActiveNode(ithNode);
                    controllers.get(i).setActiveProof(activeProof);
                    controllers.get(i).viewProofNode(ithNode);
                    final int tmp = i;
                    ithNode.optionalGet(activeProof).ifPresent(node -> {
                        String name = node.getLabel();
                        if(name == null) {
                            name = "default";
                        }
                        view.getTabs().get(tmp).setText(name);
                    });
                }
            } else if (numChildren > controllers.size()) {
                for (int i = 0; i < controllers.size(); ++i) {
                    ProofNodeSelector ithNode = new ProofNodeSelector(parentSelector, i);
                    controllers.get(i).setActiveNode(ithNode);
                    controllers.get(i).setActiveProof(activeProof);
                    controllers.get(i).viewProofNode(ithNode);
                    final int tmp = i;
                    ithNode.optionalGet(activeProof).ifPresent(node -> {
                        String name = node.getLabel();
                        if(name == null) {
                            name = "default";
                        }
                        view.getTabs().get(tmp).setText(name);
                    });
                }
                for (int i = controllers.size(); i < numChildren; ++i) {
                    ProofNodeSelector ithNode = new ProofNodeSelector(parentSelector, i);
                    SequentController controller = new SequentController(listener);
                    controllers.add(controller);
                    ithNode.optionalGet(activeProof).ifPresent(node -> {
                        String name = node.getLabel();
                        if(name == null) {
                            name = "default";
                        }
                        view.getTabs().add(new Tab(name, controller.getView()));
                    });
                    controllers.get(i).setActiveNode(ithNode);
                    controllers.get(i).setActiveProof(activeProof);
                    controllers.get(i).viewProofNode(ithNode);
                }
            } else if (numChildren < controllers.size()) {
                for (int i = 0; i < numChildren; ++i) {
                    ProofNodeSelector ithNode = new ProofNodeSelector(parentSelector, i);
                    controllers.get(i).setActiveNode(ithNode);
                    controllers.get(i).setActiveProof(activeProof);
                    controllers.get(i).viewProofNode(ithNode);
                    final int tmp = i;
                    ithNode.optionalGet(activeProof).ifPresent(node -> {
                        String name = node.getLabel();
                        if(name == null) {
                            name = "default";
                        }
                        view.getTabs().get(tmp).setText(name);
                    });
                }
                view.getTabs().remove(numChildren, controllers.size());
                while (controllers.size() > numChildren) {
                    controllers.remove(controllers.size() - 1);
                }
            }
            if (view.getTabs().size() == 1) {
                view.getTabs().get(0).setText("default");
            }
        } else {
            controllers.clear();
            view.getTabs().clear();
            ProofNodeSelector ithNode = activeNode;
            SequentController controller = new SequentController(listener);
            controllers.add(controller);
            Optional<ProofNode> opt = ithNode.optionalGet(activeProof);
            if(opt.isPresent()) {
                String name = opt.get().getLabel();
                if(name == null) {
                    name = "default";
                }
                view.getTabs().add(new Tab(name, controller.getView()));
                controllers.get(0).setActiveNode(ithNode);
                controllers.get(0).setActiveProof(activeProof);
                controllers.get(0).viewProofNode(ithNode);
            } else {
                ProofNodeSelector parent = ithNode.getParentSelector();
                if(parent != null) {
                    ithNode.getParentSelector().optionalGet(activeProof).ifPresent(proofNode -> {
                        String name = proofNode.getLabel();
                        if(name == null) {
                            name = "default";
                        }
                        view.getTabs().add(new Tab(name, controller.getView()));
                        controllers.get(0).setActiveNode(ithNode.getParentSelector());
                        controllers.get(0).setActiveProof(activeProof);
                        controllers.get(0).viewProofNode(ithNode.getParentSelector());
                    });
                }
            }
        }
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