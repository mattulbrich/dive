package edu.kit.iti.algover.sequent;

import de.jensd.fx.glyphs.GlyphsDude;
import de.jensd.fx.glyphs.fontawesome.FontAwesomeIcon;
import edu.kit.iti.algover.FxmlController;
import edu.kit.iti.algover.browser.entities.PVCEntity;
import edu.kit.iti.algover.proof.*;
import edu.kit.iti.algover.references.ProofTermReference;
import edu.kit.iti.algover.references.ReferenceGraph;
import edu.kit.iti.algover.rules.*;
import edu.kit.iti.algover.sequent.formulas.ViewFormula;
import edu.kit.iti.algover.term.Sequent;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.term.prettyprint.AnnotatedString;
import edu.kit.iti.algover.util.Pair;
import edu.kit.iti.algover.util.Quadruple;
import edu.kit.iti.algover.util.SubSelection;
import edu.kit.iti.algover.util.SubtermSelectorReplacementVisitor;
import javafx.beans.property.SimpleObjectProperty;
import javafx.fxml.FXML;
import javafx.scene.control.Label;
import javafx.scene.control.ListCell;
import javafx.scene.control.ListView;
import javafx.scene.input.KeyCode;
import javafx.util.Callback;

import java.util.ArrayList;
import java.util.List;
import java.util.stream.Collectors;

/**
 * Created by philipp on 12.07.17.
 */
public class SequentController extends FxmlController {

    private final SequentActionListener listener;

    @FXML
    private Label goalTypeLabel;
    @FXML
    private ListView<ViewFormula> antecedentView;
    @FXML
    private ListView<ViewFormula> succedentView;

    // Subselections, see their docs for clarification
    /**
     * Whichever Term was clicked to reveal dependencies in terms of
     * a Reference (as opposed to the actual TermSelector).
     * (Currently set when control-clicking something on the sequent).
     */
    private final SubSelection<ProofTermReference> selectedReference;
    /**
     * Whichever Term was clicked to reveal dependencies in terms of
     * the actual TermSelector.
     */
    private final SimpleObjectProperty<TermSelector> selectedTerm;
    /**
     * The selection for the Term that Rules may be applied to.
     * (Currently set when left-clicking something on the sequent).
     * Shows up on the top of the RuleApplication view.
     */
    private final SimpleObjectProperty<TermSelector> lastClickedTerm;

    /**
     * The selection for the Term that the mouse is currently hovering over.
     * This is used to highlight the Term that would be affected when clicked.
     */
    private final SimpleObjectProperty<AnnotatedString.TermElement> mouseOverTerm;

    // TODO: Don't save the ReferenceGraph at the sequent controller level in the future
    // it should ideally be placed somewhere in the backend, since the ProofScript's interpreter
    // has to closely work with the reference graph to keep it updated
    private ReferenceGraph referenceGraph;
    private Proof activeProof; // Maybe place it inside the Proof or PVC class instead
    private ProofNodeSelector activeNode;

    /**
     * Builds the controller and GUI for the sequent view, that is the two ListViews of
     * {@Link TopLevelFormula}s.
     * <p>
     * This loads the GUI from the .fxml resource file
     * <tt>res/edu/kit/iti/algover/sequent/SequentView.fxml</tt>.
     *
     * @param listener
     */
    public SequentController(SequentActionListener listener) {
        super("SequentView.fxml");
        this.listener = listener;
        this.activeProof = null;
        this.referenceGraph = new ReferenceGraph();
        this.selectedReference = new SubSelection<>(listener::onRequestReferenceHighlighting);
        this.lastClickedTerm = new SimpleObjectProperty<>(null);
        this.selectedTerm = new SimpleObjectProperty<>(null);
        this.selectedTerm.addListener((observable, oldValue, newValue) -> listener.onClickSequentSubterm(newValue));
        // We don't care about the particular mouse-over selected term, that's why we won't do anything on events.
        // Our children however need to communicate somehow and share a common selected item.
        mouseOverTerm = new SimpleObjectProperty<>(null);

        antecedentView.setCellFactory(makeTermCellFactory());
        succedentView.setCellFactory(makeTermCellFactory());

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
     * Adds a style class for a certain Term.
     * @param ts A termselector pointing to the term to be styled.
     * @param styleClass The style class to be applied (has to be found int style.css
     * @param prio A priority of the Style (determines which style will be applied when styles clash)
     * @param id An id to remove the style later on.
     */
    public void addStyleForTerm(TermSelector ts, String styleClass, int prio, String id) {
        List<BasicFormulaView> formulaViews = null;
        if(ts.getPolarity() == TermSelector.SequentPolarity.ANTECEDENT) {
            formulaViews = antecedentView.getChildrenUnmodifiable().stream().map(x -> (BasicFormulaView)x).collect(Collectors.toList());
        } else {
            formulaViews = antecedentView.getChildrenUnmodifiable().stream().map(x -> (BasicFormulaView)x).collect(Collectors.toList());
        }
        formulaViews.get(ts.getTermNo()).addStyleForTerm(ts, styleClass, prio, id);
    }

    /**
     * Removes a Style from a FormulaView
     * @param ts a TermSelector that points at least to the formula the style should be removed from
     * @param id the id of the style to remove (see {@link #addStyleForTerm(TermSelector, String, int, String)})
     */
    public void removeStyle(TermSelector ts, String id) {
        List<BasicFormulaView> formulaViews = null;
        if(ts.getPolarity() == TermSelector.SequentPolarity.ANTECEDENT) {
            formulaViews = antecedentView.getChildrenUnmodifiable().stream().map(x -> (BasicFormulaView)x).collect(Collectors.toList());
        } else {
            formulaViews = antecedentView.getChildrenUnmodifiable().stream().map(x -> (BasicFormulaView)x).collect(Collectors.toList());
        }
        formulaViews.get(ts.getTermNo()).removeStyle(id);
    }

    /**
     * Applies a styleClass to a given Term (styles added like this will be overwritten with the next style to avoid this use add style instead)
     * @param ts A Termselector pointing to the term to be styled
     * @param styleClass the styleclass to be applied
     */
    public void setStyleForTerm(TermSelector ts, String styleClass) {
        List<BasicFormulaView> formulaViews = null;
        if(ts.getPolarity() == TermSelector.SequentPolarity.ANTECEDENT) {
            formulaViews = antecedentView.getChildrenUnmodifiable().stream().map(x -> (BasicFormulaView)x).collect(Collectors.toList());
        } else {
            formulaViews = antecedentView.getChildrenUnmodifiable().stream().map(x -> (BasicFormulaView)x).collect(Collectors.toList());
        }
        formulaViews.get(ts.getTermNo()).setStyleForTerm(ts, styleClass);
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
            referenceGraph = new ReferenceGraph();
            referenceGraph.addFromReferenceMap(pvcEntity.getLocation(), pvc.getReferenceMap());
        }
    }

    public void forceViewSequentForPVC(PVCEntity entity, Proof proof) {
        activeProof = null;
        viewSequentForPVC(entity, proof);
    }

    public void setReferenceGraph(ReferenceGraph graph) {
        referenceGraph = graph;
    }

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
                if(lastClickedTerm.get() != null && lastClickedTerm.get().isValidForSequent(getActiveNode().getSequent())) {
                    listener.onClickSequentSubterm(lastClickedTerm.get());
                }
            } catch (RuleException e) {
                e.printStackTrace(); // should not happen, as long as the activeNode selector is correct
                return;
            }
            updateGoalTypeLabel();
        }
    }


    /**
     * View a preview for a rule application. This highlights the added/removed {@link ViewFormula}s
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
                ProofRuleApplication application = proofNode.getPsr();
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
        antecedentView.getItems().setAll(calculateAssertions(sequent.getAntecedent(), TermSelector.SequentPolarity.ANTECEDENT, branchInfo));
        List<ViewFormula> after = calculateAssertions(sequent.getSuccedent(), TermSelector.SequentPolarity.SUCCEDENT, branchInfo);
        succedentView.getItems().setAll(after);
    }

    private List<ViewFormula> calculateAssertions(List<ProofFormula> proofFormulas, TermSelector.SequentPolarity polarity, BranchInfo branchInfo) {
        ArrayList<ViewFormula> formulas = new ArrayList<>(proofFormulas.size());

        int deletedFormulas = 0;

        // Render original, modified and deleted proof formulas
        formulaLoop:
        for (int i = 0; i < proofFormulas.size(); i++) {
            // Short-circuit this loop if there is a ModifiedFormula to be built instead.
            if (branchInfo != null) {
                Term term = proofFormulas.get(i).getTerm();
                List<TermSelector> modifiedParts = new ArrayList<>();

                for (Pair<TermSelector, Term> replacementPair : branchInfo.getReplacements()) {
                    // If there were replacements for the current term
                    if (replacementPair.getFst().getPolarity() == polarity && replacementPair.getFst().getTermNo() == i) {

                        // This algorithm assumes that there are no replacements _within_ other replacements
                        // I _really_ think that's a reasonable assumption. Maybe there should be documentation
                        // and / or a test for that invariant in ProofRuleApplication?
                        SubtermSelectorReplacementVisitor replacmentVisitor = new SubtermSelectorReplacementVisitor(replacementPair.getSnd());
                        try {
                            term = term.accept(replacmentVisitor, replacementPair.getFst().getSubtermSelector());
                            modifiedParts.add(replacementPair.getFst());
                        } catch (RuleException e) {
                            // In this case the SubtermSelector did not fit the Term!
                            throw new RuntimeException(e);
                        }
                    }
                }

                if (!modifiedParts.isEmpty()) {
                    formulas.add(new ViewFormula(i, term, ViewFormula.Type.CHANGED, polarity, modifiedParts));
                    continue formulaLoop;
                }

                List<ProofFormula> deletions = polarity == TermSelector.SequentPolarity.ANTECEDENT
                        ? branchInfo.getDeletions().getAntecedent()
                        : branchInfo.getDeletions().getSuccedent();

                for (ProofFormula deleted : deletions) {
                    if (proofFormulas.get(i).getTerm().equals(deleted.getTerm())) {
                        formulas.add(new ViewFormula(-1, deleted.getTerm(), ViewFormula.Type.DELETED, polarity));
                        deletedFormulas++;
                        continue formulaLoop;
                    }
                }
            }
            formulas.add(new ViewFormula(i, proofFormulas.get(i).getTerm(), ViewFormula.Type.ORIGINAL, polarity));
        }

        // render additions on the sequent
        if (branchInfo != null) {
            List<ProofFormula> additions = polarity == TermSelector.SequentPolarity.ANTECEDENT
                    ? branchInfo.getAdditions().getAntecedent()
                    : branchInfo.getAdditions().getSuccedent();

            for (ProofFormula addition : additions) {
                formulas.add(new ViewFormula(formulas.size() - deletedFormulas, addition.getTerm(), ViewFormula.Type.ADDED, polarity));
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


    private Callback<ListView<ViewFormula>, ListCell<ViewFormula>> makeTermCellFactory() {
        return listView -> new FormulaCell(selectedTerm);
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

    public ReferenceGraph getReferenceGraph() {
        return referenceGraph;
    }

    public Proof getActiveProof() {
        return activeProof;
    }

    public SubSelection<ProofTermReference> referenceSelection() {
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

}
