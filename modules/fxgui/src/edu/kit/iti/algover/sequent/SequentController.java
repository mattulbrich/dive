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
import edu.kit.iti.algover.script.interpreter.Interpreter;
import edu.kit.iti.algover.term.Sequent;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.term.prettyprint.AnnotatedString;
import edu.kit.iti.algover.util.SubSelection;
import javafx.fxml.FXML;
import javafx.scene.control.ListView;
import javafx.scene.input.KeyCode;

import java.util.List;
import java.util.stream.Collectors;

/**
 * Created by philipp on 12.07.17.
 */
public class SequentController extends FxmlController {

    private final SequentActionListener listener;

    @FXML private ListView<Term> antecedentView;
    @FXML private ListView<Term> succedentView;

    private final SubSelection<ProofTermReference> selectedReference;
    private final SubSelection<TermSelector> selectedTerm;
    private final SubSelection<TermSelector> lastClickedTerm;
    private final SubSelection<AnnotatedString.TermElement> highlightedTerm;
    private ReferenceGraph referenceGraph;
    private Proof activeProof;
    private ProofNode activeNode;

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

        antecedentView.setCellFactory(termListView -> createTermCell(TermSelector.SequentPolarity.ANTECEDENT, termListView));
        succedentView.setCellFactory(termListView -> createTermCell(TermSelector.SequentPolarity.SUCCEDENT, termListView));

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
            activeNode = activeProof.getProofRoot();
            updateSequent(activeNode.getSequent());
            referenceGraph = new ReferenceGraph();
            referenceGraph.addFromReferenceMap(pvcEntity.getLocation(), pvc.getReferenceMap());
        }
    }

    // What a method name
    public void tryMovingOn() {
        if (activeNode != null && activeNode.getChildren().size() > 0) {
            activeNode = activeNode.getChildren().get(0);
            updateSequent(activeNode.getSequent());
        }
    }
    private void updateSequent(Sequent sequent) {
        antecedentView.getItems().setAll(calculateAssertions(sequent.getAntecedent()));
        succedentView.getItems().setAll(calculateAssertions(sequent.getSuccedent()));
    }

    private TermCell createTermCell(TermSelector.SequentPolarity polarity, ListView<Term> termListView) {
        return new TermCell(polarity, selectedTerm, lastClickedTerm, highlightedTerm);
    }

    private ProofTermReference attachCurrentActiveProof(TermSelector selector) {
        if (activeNode != null) {
            ProofNodeSelector nodeSelector = new ProofNodeSelector(activeNode);
            return new ProofTermReference(nodeSelector, selector);
        }
        return null;
    }

    private TermSelector termSelectorFromReference(ProofTermReference reference) {
        try {
            if (activeProof != null && reference.getProofNodeSelector().get(activeProof) == activeNode) {
                return reference.getTermSelector();
            } else {
                return null;
            }
        } catch (RuleException e) {
            e.printStackTrace();
            // TODO: Maybe error handling?
            return null;
        }
    }

    private List<Term> calculateAssertions(List<ProofFormula> proofFormulas) {
        return proofFormulas.stream().map(ProofFormula::getTerm).collect(Collectors.toList());
    }

    public ProofNode getActiveProofNode() {
        return activeNode;
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
