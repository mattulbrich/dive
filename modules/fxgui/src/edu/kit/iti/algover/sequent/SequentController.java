package edu.kit.iti.algover.sequent;

import edu.kit.iti.algover.FxmlController;
import edu.kit.iti.algover.browser.entities.PVCEntity;
import edu.kit.iti.algover.proof.*;
import edu.kit.iti.algover.references.ProofTermReference;
import edu.kit.iti.algover.references.ReferenceGraph;
import edu.kit.iti.algover.rules.BranchInfo;
import edu.kit.iti.algover.rules.ProofRuleApplication;
import edu.kit.iti.algover.rules.RuleException;
import edu.kit.iti.algover.rules.TermSelector;
import edu.kit.iti.algover.term.Sequent;
import edu.kit.iti.algover.term.prettyprint.AnnotatedString;
import edu.kit.iti.algover.util.SubSelection;
import javafx.fxml.FXML;
import javafx.scene.control.ListCell;
import javafx.scene.control.ListView;
import javafx.scene.input.KeyCode;
import javafx.util.Callback;

import java.util.ArrayList;
import java.util.List;

/**
 * Created by philipp on 12.07.17.
 */
public class SequentController extends FxmlController {

    private final SequentActionListener listener;

    @FXML private ListView<TopLevelFormula> antecedentView;
    @FXML private ListView<TopLevelFormula> succedentView;

    private final SubSelection<ProofTermReference> selectedReference;
    private final SubSelection<TermSelector> selectedTerm;
    private final SubSelection<TermSelector> lastClickedTerm;
    private final SubSelection<AnnotatedString.TermElement> highlightedTerm;
    private ReferenceGraph referenceGraph;
    private Proof activeProof;
    private ProofNodeSelector activeNode;

    public SequentController(SequentActionListener listener) {
        super("SequentView.fxml");
        this.listener = listener;
        this.activeProof = null;
        this.referenceGraph = new ReferenceGraph();
        this.selectedReference = new SubSelection<>(listener::onRequestReferenceHighlighting);
        this.selectedTerm = selectedReference.subSelection(this::termSelectorFromReference, this::attachCurrentActiveProof);
        this.lastClickedTerm = new SubSelection<>(listener::onClickSequentSubterm);
        // We don't care about the particular mouse-over selected term, that's why we won't do anything on events.
        // Our children however need to communicate somehow and share a common selected item.
        this.highlightedTerm = new SubSelection<>(r -> {});

        antecedentView.setCellFactory(makeTermCellFactory(TermSelector.SequentPolarity.ANTECEDENT));
        succedentView.setCellFactory(makeTermCellFactory(TermSelector.SequentPolarity.SUCCEDENT));

        antecedentView.setOnKeyPressed(keyEvent -> {
            if (keyEvent.getCode() == KeyCode.ESCAPE) {
                antecedentView.getSelectionModel().select(null);
            }
        });
        succedentView.setOnKeyPressed(keyEvent -> {
            if (keyEvent.getCode() == KeyCode.ESCAPE) {
                succedentView.getSelectionModel().select(null);
            }
        });
    }

    public void viewSequentForPVC(PVCEntity pvcEntity, Proof proof) {
        PVC pvc = pvcEntity.getPVC();
        if (activeProof == null || !activeProof.getPvcName().equals(pvc.getIdentifier())) {
            activeProof = proof;
            activeNode = new ProofNodeSelector();
            updateSequent(getActiveNode().getSequent(), null);
            referenceGraph = new ReferenceGraph();
            referenceGraph.addFromReferenceMap(pvcEntity.getLocation(), pvc.getReferenceMap());
        }
    }

    // What a method name
    public void tryMovingOn() {
        if (activeNode != null) {
            ProofNodeSelector newActiveNode = new ProofNodeSelector(activeNode, 0);
            try {
                ProofNode node = newActiveNode.get(activeProof);
                updateSequent(node.getSequent(), null);
                activeNode = newActiveNode;
            } catch (RuleException e) {
                return;
            }
        }
    }

    public ProofNode getActiveNode() {
        try {
            return activeNode.get(activeProof);
        } catch (RuleException e) {
            throw new RuntimeException(e);
        }
    }

    public void viewProofApplicationPreview(ProofRuleApplication application) {
        try {
            updateSequent(activeNode.get(activeProof).getSequent(), application.getBranchInfo().get(0));
        } catch (RuleException e) {
            e.printStackTrace();
        }
    }

    private void updateSequent(Sequent sequent, BranchInfo branchInfo) {
        antecedentView.getItems().setAll(calculateAssertions(sequent.getAntecedent()));
        succedentView.getItems().setAll(calculateAssertions(sequent.getSuccedent()));
        if (branchInfo != null) {
            for (ProofFormula addition : branchInfo.getAdditions().getAntecedent()) {
                antecedentView.getItems().add(new TopLevelFormula(0, addition.getTerm(), TopLevelFormula.ChangeType.ADDED));
            }
            for (ProofFormula deletion : branchInfo.getDeletions().getAntecedent()) {
                succedentView.getItems().add(new TopLevelFormula(0, deletion.getTerm(), TopLevelFormula.ChangeType.DELETED));
            }
        }
    }

    private Callback<ListView<TopLevelFormula>, ListCell<TopLevelFormula>> makeTermCellFactory(TermSelector.SequentPolarity polarity) {
        return listView -> new TermCell(polarity, selectedTerm, lastClickedTerm, highlightedTerm);
    }

    private ProofTermReference attachCurrentActiveProof(TermSelector selector) {
        if (activeNode != null) {
            return new ProofTermReference(activeNode, selector);
        }
        return null;
    }

    private TermSelector termSelectorFromReference(ProofTermReference reference) {
        if (activeProof != null && reference.getProofNodeSelector() == activeNode) {
            return reference.getTermSelector();
        } else {
            return null;
        }
    }

    private List<TopLevelFormula> calculateAssertions(List<ProofFormula> proofFormulas) {
        ArrayList<TopLevelFormula> formulas = new ArrayList<>(proofFormulas.size());
        for (int i = 0; i < proofFormulas.size(); i++) {
            // Create a "default" kind of top-level-formula
            // one that does not have a tag for being added / deleted / modified, so gets rendered normally.
            formulas.add(new TopLevelFormula(i, proofFormulas.get(i).getTerm()));
        }
        return formulas;
    }

    public ReferenceGraph getReferenceGraph() {
        return referenceGraph;
    }

    public Proof getActiveProof() {
        return activeProof;
    }

    public SubSelection<ProofTermReference> referenceSelection() {
        return selectedReference;
    }
}
