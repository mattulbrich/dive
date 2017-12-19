package edu.kit.iti.algover.sequent;

import edu.kit.iti.algover.FxmlController;
import edu.kit.iti.algover.browser.entities.PVCEntity;
import edu.kit.iti.algover.proof.*;
import edu.kit.iti.algover.references.ProofTermReference;
import edu.kit.iti.algover.references.ReferenceGraph;
import edu.kit.iti.algover.rules.*;
import edu.kit.iti.algover.rules.impl.SubstitutionVisitor;
import edu.kit.iti.algover.sequent.formulas.AddedOrDeletedFormula;
import edu.kit.iti.algover.sequent.formulas.ModifiedFormula;
import edu.kit.iti.algover.sequent.formulas.OriginalFormula;
import edu.kit.iti.algover.sequent.formulas.TopLevelFormula;
import edu.kit.iti.algover.term.Sequent;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.term.TermVisitor;
import edu.kit.iti.algover.term.builder.ReplacementVisitor;
import edu.kit.iti.algover.term.prettyprint.AnnotatedString;
import edu.kit.iti.algover.util.Pair;
import edu.kit.iti.algover.util.SubSelection;
import edu.kit.iti.algover.util.SubtermSelectorReplacementVisitor;
import javafx.fxml.FXML;
import javafx.scene.control.ListCell;
import javafx.scene.control.ListView;
import javafx.scene.input.KeyCode;
import javafx.util.Callback;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

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
    private final SubSelection<AnnotatedString.TermElement> mouseOverTerm;
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
        this.mouseOverTerm = new SubSelection<>(r -> {});

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

    public void resetProofApplicationPreview() {
        try {
            updateSequent(activeNode.get(activeProof).getSequent(), null);
        } catch (RuleException e) {
            e.printStackTrace();
        }
    }

    private void updateSequent(Sequent sequent, BranchInfo branchInfo) {
        antecedentView.getItems().setAll(calculateAssertions(sequent.getAntecedent(), TermSelector.SequentPolarity.ANTECEDENT, branchInfo));
        succedentView.getItems().setAll(calculateAssertions(sequent.getSuccedent(), TermSelector.SequentPolarity.SUCCEDENT, branchInfo));
    }

    private List<TopLevelFormula> calculateAssertions(List<ProofFormula> proofFormulas, TermSelector.SequentPolarity polarity, BranchInfo branchInfo) {
        ArrayList<TopLevelFormula> formulas = new ArrayList<>(proofFormulas.size());
        formulaLoop: for (int i = 0; i < proofFormulas.size(); i++) {
            // Short-circuit this loop if there is a ModifiedFormula to be built instead.
            if (branchInfo != null) {
                // FIXME this makes the assumption that there will only ever by 1 replacement per top-level formula!
                // maybe this is reasonable, but that should maybe be made more explicit if it is.
                for (Pair<TermSelector, Term> replacementPair : branchInfo.getReplacements()) {
                    if (replacementPair.getFst().getPolarity() == polarity && replacementPair.getFst().getTermNo() == i) {
                        SubtermSelectorReplacementVisitor replacmentVisitor = new SubtermSelectorReplacementVisitor(replacementPair.getSnd());
                        try {
                            Term newTerm = proofFormulas.get(i).getTerm().accept(replacmentVisitor, replacementPair.getFst().getSubtermSelector());
                            formulas.add(new ModifiedFormula(replacementPair.getFst().getSubtermSelector(), newTerm));
                        } catch (RuleException e) {
                            // In this case the SubtermSelector did not fit the Term!
                            new RuntimeException(e);
                        }
                        continue formulaLoop;
                    }
                }
            }
            formulas.add(new OriginalFormula(i, proofFormulas.get(i).getTerm()));
        }
        if (branchInfo != null) {
            List<ProofFormula> additions = polarity == TermSelector.SequentPolarity.ANTECEDENT
                    ? branchInfo.getAdditions().getAntecedent()
                    : branchInfo.getAdditions().getSuccedent();
            List<ProofFormula> deletions = polarity == TermSelector.SequentPolarity.SUCCEDENT
                    ? branchInfo.getDeletions().getSuccedent()
                    : branchInfo.getDeletions().getSuccedent();

            for (ProofFormula addition : additions) {
                formulas.add(new AddedOrDeletedFormula(AddedOrDeletedFormula.Type.ADDED, addition.getTerm()));
            }
            for (ProofFormula deletion : deletions) {
                formulas.add(new AddedOrDeletedFormula(AddedOrDeletedFormula.Type.DELETED, deletion.getTerm()));
            }
        }
        return formulas;
    }

    private Callback<ListView<TopLevelFormula>, ListCell<TopLevelFormula>> makeTermCellFactory(TermSelector.SequentPolarity polarity) {
        return listView -> new FormulaCell(polarity, selectedTerm, lastClickedTerm, mouseOverTerm);
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
