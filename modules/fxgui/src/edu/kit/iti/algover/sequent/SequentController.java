package edu.kit.iti.algover.sequent;

import de.jensd.fx.glyphs.GlyphsDude;
import de.jensd.fx.glyphs.fontawesome.FontAwesomeIcon;
import edu.kit.iti.algover.FxmlController;
import edu.kit.iti.algover.browser.entities.PVCEntity;
import edu.kit.iti.algover.proof.*;
import edu.kit.iti.algover.references.ProofTermReferenceTarget;
import edu.kit.iti.algover.rules.*;
import edu.kit.iti.algover.sequent.formulas.AddedFormula;
import edu.kit.iti.algover.sequent.formulas.DeletedFormula;
import edu.kit.iti.algover.sequent.formulas.ModifiedFormula;
import edu.kit.iti.algover.sequent.formulas.OriginalFormula;
import edu.kit.iti.algover.sequent.formulas.TopLevelFormula;
import edu.kit.iti.algover.term.Sequent;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.term.prettyprint.AnnotatedString;
import edu.kit.iti.algover.util.Pair;
import edu.kit.iti.algover.util.SubSelection;
import edu.kit.iti.algover.util.SubtermSelectorReplacementVisitor;
import javafx.collections.FXCollections;
import javafx.collections.ObservableSet;
import javafx.fxml.FXML;
import javafx.scene.control.Label;
import javafx.scene.control.ListCell;
import javafx.scene.control.ListView;
import javafx.scene.input.KeyCode;
import javafx.util.Callback;

import java.util.*;
import java.util.stream.Collectors;

/**
 * Created by philipp on 12.07.17.
 */
public class SequentController extends FxmlController {

    private final SequentActionListener listener;

    @FXML
    private Label goalTypeLabel;
    @FXML
    private ListView<TopLevelFormula> antecedentView;
    @FXML
    private ListView<TopLevelFormula> succedentView;

    // Subselections, see their docs for clarification
    /**
     * Whichever Term was clicked to reveal dependencies in terms of
     * a Reference (as opposed to the actual TermSelector).
     * (Currently set when control-clicking something on the sequent).
     */
    private final SubSelection<ProofTermReferenceTarget> selectedReference;
    /**
     * Whichever Term was clicked to reveal dependencies in terms of
     * the actual TermSelector.
     */
    private final SubSelection<TermSelector> selectedTerm;
    /**
     * The selection for the Term that Rules may be applied to.
     * (Currently set when left-clicking something on the sequent).
     * Shows up on the top of the RuleApplication view.
     */
    private final SubSelection<TermSelector> lastClickedTerm;
    /**
     * The selection for the Term that the mouse is currently hovering over.
     * This is used to highlight the Term that would be affected when clicked.
     */
    private final SubSelection<AnnotatedString.TermElement> mouseOverTerm;


    private Proof activeProof; // Maybe place it inside the Proof or PVC class instead
    private ProofNodeSelector activeNode;

    private ObservableSet<TermSelector> historyHighlightsAntec = FXCollections.observableSet();
    private ObservableSet<TermSelector> historyHighlightsSucc = FXCollections.observableSet();

    /**
     * Builds the controller and GUI for the sequent view, that is the two ListViews of
     * {@Link TopLevelFormula}s.
     * <p>
     * This loads the GUI from the .fxml resource file
     * <tt>res/edu/kit/iti/algover/sequent/SequentView.fxml</tt>.
     *
     * @param listener
     *
     */
    public SequentController(SequentActionListener listener) {
        super("SequentView.fxml");
        this.listener = listener;
        this.activeProof = null;
        //this.referenceGraph = new ReferenceGraph();
        this.selectedReference = new SubSelection<>(listener::onRequestReferenceHighlighting);
        this.selectedTerm = selectedReference.subSelection(this::termSelectorFromReference, this::attachCurrentActiveProof);
        this.lastClickedTerm = new SubSelection<>(listener::onClickSequentSubterm);
        // We don't care about the particular mouse-over selected term, that's why we won't do anything on events.
        // Our children however need to communicate somehow and share a common selected item.
        this.mouseOverTerm = new SubSelection<>(r -> {
        });

        antecedentView.setCellFactory(makeTermCellFactory(TermSelector.SequentPolarity.ANTECEDENT, historyHighlightsAntec));
        succedentView.setCellFactory(makeTermCellFactory(TermSelector.SequentPolarity.SUCCEDENT, historyHighlightsSucc));

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

    /**
     * Fills the ListViews with the formulas in the very first sequent (from the root
     * of the {@link ProofNode} tree).
     *
     * @param pvcEntity the PVC for which to show the root sequent
     * @param proof     the existing proof or proof stub for the pvc
     */
    public void viewSequentForPVC(PVCEntity pvcEntity, Proof proof) {
        PVC pvc = pvcEntity.getPVC();
        if (activeProof == null || !activeProof.getPVCName().equals(pvc.getIdentifier())) {
            activeProof = proof;
            activeNode = new ProofNodeSelector();
            updateSequent(getActiveNode().getSequent(), null);
            //referenceGraph = new ReferenceGraph();
            //referenceGraph = proof.getGraph();
            //referenceGraph.addFromReferenceMap(pvcEntity.getLocation(), pvc.getReferenceMap());
        }
    }

    public void forceViewSequentForPVC(PVCEntity entity, Proof proof) {
        activeProof = null;
        viewSequentForPVC(entity, proof);
    }

    //@Deprecated
   // public void setReferenceGraph(ReferenceGraph graph) {
   //     referenceGraph = graph;
   // }

    //SaG: was used before having exhaustive RuleApp; Remove later if no Bug is found!
    @Deprecated
    public void tryMovingOn() {
        if (activeNode != null) {
            try {
                ProofNode nodeBefore = activeNode.get(activeProof);

                if (nodeBefore.getChildren().size() == 1) {
                    ProofNodeSelector newActiveNode = new ProofNodeSelector(activeNode, 0);
                    ProofNode node = newActiveNode.get(activeProof);
                    updateSequent(node.getSequent(), null);
                    activeNode = newActiveNode;
                }
            } catch (RuleException e) {
                e.printStackTrace(); // should not happen, as long as the activeNode selector is correct
                return;
            }
            updateGoalTypeLabel();
        }
    }

    public void tryMovingOnEx() {
        if (activeNode != null) {
            try {
                ProofNode nodeBefore = activeNode.get(activeProof);
                while (nodeBefore.getChildren().size() > 0) {
                    ProofNodeSelector newActiveNode = new ProofNodeSelector(activeNode, 0);
                    ProofNode node = newActiveNode.get(activeProof);
                    updateSequent(node.getSequent(), null);
                    activeNode = newActiveNode;
                    nodeBefore = activeNode.get(activeProof);
                }
                listener.onSwitchViewedNode(activeNode);
                if(lastClickedTerm.selected().get() != null && lastClickedTerm.selected().get().isValidForSequent(getActiveNode().getSequent())) {
                    listener.onClickSequentSubterm(lastClickedTerm.selected().get());
                }
            } catch (RuleException e) {
                e.printStackTrace(); // should not happen, as long as the activeNode selector is correct
                return;
            }
            updateGoalTypeLabel();
        }
    }


    /**
     * View a preview for a rule application. This highlights the added/removed {@link TopLevelFormula}s
     * and changed {@link Term}s.
     * <p>
     * If the application has no {@link BranchInfo}s (because it is a closing rule, for example), then
     * it does not update the view.
     *
     * @param application a proof rule instantiation to read the changes from (via their {@link ProofRuleApplication#getBranchInfo()}).
     */
    public void viewProofApplicationPreview(ProofRuleApplication application) {
        if (application.getBranchInfo().size() > 0) {
            try {
                updateSequent(activeNode.get(activeProof).getSequent(), application.getBranchInfo().get(0));
                updateGoalTypeLabel();
            } catch (RuleException e) {
                e.printStackTrace();
            }
        }
    }

    /**
     * Removes any highlighting added by the {@link #viewProofApplicationPreview(ProofRuleApplication)} method.
     */
    public void resetProofApplicationPreview() {
        try {
            updateSequent(activeNode.get(activeProof).getSequent(), null);
            updateGoalTypeLabel();
        } catch (RuleException e) {
            e.printStackTrace();
        }
    }

    public void viewProofNode(ProofNodeSelector proofNodeSelector) {
        ProofNodeSelector selector = proofNodeSelector.getParentSelector();
        if(selector == null) {
            selector = proofNodeSelector;
        }
        selector.optionalGet(activeProof).ifPresent(parentNode -> {
            proofNodeSelector.optionalGet(activeProof).ifPresent(proofNode -> {
                activeNode = proofNodeSelector;
                BranchInfo branchInfo = null;
                ProofRuleApplication application = proofNode.getProofRuleApplication();
                if (application != null) {
                    branchInfo = application.getBranchInfo().get(
                            proofNodeSelector.getPath()[proofNodeSelector.getPath().length - 1]
                    );
                }
                updateSequent(parentNode.getSequent(), branchInfo);
                updateGoalTypeLabel();
            });
        });
    }

    private void updateSequent(Sequent sequent, BranchInfo branchInfo) {
        List<TopLevelFormula> col = calculateAssertions(sequent.getAntecedent(), TermSelector.SequentPolarity.ANTECEDENT, branchInfo);
        antecedentView.getItems().setAll(col);
        List<TopLevelFormula> after = calculateAssertions(sequent.getSuccedent(), TermSelector.SequentPolarity.SUCCEDENT, branchInfo);
        succedentView.getItems().setAll(after);
    }

    private List<TopLevelFormula> calculateAssertions(List<ProofFormula> proofFormulas, TermSelector.SequentPolarity polarity, BranchInfo branchInfo) {
        ArrayList<TopLevelFormula> formulas = new ArrayList<>(proofFormulas.size());

        int deletedFormulas = 0;

        // Render original, modified and deleted proof formulas
        formulaLoop:
        for (int i = 0; i < proofFormulas.size(); i++) {
            // Short-circuit this loop if there is a ModifiedFormula to be built instead.
            if (branchInfo != null) {
                Term term = proofFormulas.get(i).getTerm();
                List<SubtermSelector> modifiedParts = new ArrayList<>();

                for (Pair<TermSelector, Term> replacementPair : branchInfo.getReplacements()) {
                    // If there were replacements for the current term
                    if (replacementPair.getFst().getPolarity() == polarity && replacementPair.getFst().getTermNo() == i) {

                        // This algorithm assumes that there are no replacements _within_ other replacements
                        // I _really_ think that's a reasonable assumption. Maybe there should be documentation
                        // and / or a test for that invariant in ProofRuleApplication?
                        SubtermSelectorReplacementVisitor replacmentVisitor = new SubtermSelectorReplacementVisitor(replacementPair.getSnd());
                        try {
                            term = term.accept(replacmentVisitor, replacementPair.getFst().getSubtermSelector());
                            modifiedParts.add(replacementPair.getFst().getSubtermSelector());
                        } catch (RuleException e) {
                            // In this case the SubtermSelector did not fit the Term!
                            throw new RuntimeException(e);
                        }
                    }
                }

                if (!modifiedParts.isEmpty()) {
                    formulas.add(new ModifiedFormula(modifiedParts, term, i));
                    continue formulaLoop;
                }

                List<ProofFormula> deletions = polarity == TermSelector.SequentPolarity.ANTECEDENT
                        ? branchInfo.getDeletions().getAntecedent()
                        : branchInfo.getDeletions().getSuccedent();

                for (ProofFormula deleted : deletions) {
                    if (proofFormulas.get(i).getTerm().equals(deleted.getTerm())) {
                        formulas.add(new DeletedFormula(deleted.getTerm()));
                        deletedFormulas++;
                        continue formulaLoop;
                    }
                }
            }
            formulas.add(new OriginalFormula(i, proofFormulas.get(i).getTerm()));
        }

        // render additions on the sequent
        if (branchInfo != null) {
            List<ProofFormula> additions = polarity == TermSelector.SequentPolarity.ANTECEDENT
                    ? branchInfo.getAdditions().getAntecedent()
                    : branchInfo.getAdditions().getSuccedent();

            for (ProofFormula addition : additions) {
                formulas.add(new AddedFormula(formulas.size() - deletedFormulas, addition.getTerm()));
            }
        }
        return formulas;
    }

    private void updateGoalTypeLabel() {
        try {
            ProofNode node = activeNode.get(activeProof);
            if (node.getChildren().size() == 0) {
                if (node.isClosed()) {
                    goalTypeLabel.setText("Closed Goal");
                    goalTypeLabel.setGraphic(GlyphsDude.createIcon(FontAwesomeIcon.CHECK));
                } else {
                    goalTypeLabel.setText("Open Goal");
                    goalTypeLabel.setGraphic(GlyphsDude.createIcon(FontAwesomeIcon.BULLSEYE));
                }
            } else {
                goalTypeLabel.setText("Node");
                goalTypeLabel.setGraphic(null);
            }
        } catch (RuleException e) {
            System.err.println("Invalid ProofNodeSelector generated");
            e.printStackTrace();
            return;
        }
    }


    private Callback<ListView<TopLevelFormula>, ListCell<TopLevelFormula>> makeTermCellFactory(TermSelector.SequentPolarity polarity, ObservableSet<TermSelector> historyHighlights) {
        return listView -> new FormulaCell(polarity, selectedTerm, lastClickedTerm, mouseOverTerm, historyHighlights);
    }

    private ProofTermReferenceTarget attachCurrentActiveProof(TermSelector selector) {
        if (activeNode != null) {
            return new ProofTermReferenceTarget(activeNode, selector);
        }
        return null;
    }

    private TermSelector termSelectorFromReference(ProofTermReferenceTarget reference) {
        if (activeProof != null && reference.getProofNodeSelector() == activeNode) {
            return reference.getTermSelector();
        } else {
            return null;
        }
    }

    public void clear() {
        antecedentView.getItems().clear();
        succedentView.getItems().clear();
    }

    public ProofNode getActiveNode() {
        try {
            return activeNode.get(activeProof);
        } catch (RuleException e) {
            throw new RuntimeException(e);
        }
    }

 /*   public ReferenceGraph getReferenceGraph() {
        return referenceGraph;
    }*/

    public Proof getActiveProof() {
        return activeProof;
    }

    public SubSelection<ProofTermReferenceTarget> referenceSelection() {
        return selectedReference;
    }

    public void setActiveNode(ProofNodeSelector pns) {
        activeNode = pns;
    }

    public void setActiveProof(Proof p) {
        activeProof = p;
    }

    public ProofNodeSelector getActiveNodeSelector() {
        return activeNode;
    }

    public void updateSequentController(ProofNodeSelector selector, Proof activeProof, Set<ProofTermReferenceTarget> collect) {
        this.setActiveNode(selector);
        this.setActiveProof(activeProof);
        Set<TermSelector> collect1 = collect.stream().map(ProofTermReferenceTarget::getTermSelector).collect(Collectors.toSet());
       // System.out.println("collect1.size = " + collect1.size());
        this.setHistoryHighlights(FXCollections.observableSet(collect1));
        this.viewProofNode(selector);


    }

    /**
     * Set the information which term to highlight for history highlighting. This method already divides the information acc. to teh sequent polarity
     */
    private void setHistoryHighlights(ObservableSet<TermSelector> collect) {
        this.historyHighlightsAntec.clear();
        this.historyHighlightsSucc.clear();
        Set<TermSelector> antec = collect.stream().filter(termSelector -> termSelector.getPolarity() == TermSelector.SequentPolarity.ANTECEDENT).collect(Collectors.toSet());
        Set<TermSelector> succ = collect.stream().filter(termSelector -> termSelector.getPolarity() == TermSelector.SequentPolarity.SUCCEDENT).collect(Collectors.toSet());
        this.historyHighlightsAntec.addAll(antec);
        this.historyHighlightsSucc.addAll(succ);
        //        this.historyHighlights.addAll(collect);
    }
}
