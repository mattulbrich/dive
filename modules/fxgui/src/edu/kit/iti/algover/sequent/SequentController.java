/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.sequent;

import de.jensd.fx.glyphs.fontawesome.FontAwesomeIcon;
import de.jensd.fx.glyphs.fontawesome.utils.FontAwesomeIconFactory;
import edu.kit.iti.algover.FxmlController;
import edu.kit.iti.algover.MainController;
import edu.kit.iti.algover.PropertyManager;
import edu.kit.iti.algover.proof.PVC;
import edu.kit.iti.algover.proof.Proof;
import edu.kit.iti.algover.proof.ProofFormula;
import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.proof.ProofNodeSelector;
import edu.kit.iti.algover.proof.ProofStatus;
import edu.kit.iti.algover.references.ProofTermReferenceTarget;
import edu.kit.iti.algover.rules.BranchInfo;
import edu.kit.iti.algover.rules.ProofRuleApplication;
import edu.kit.iti.algover.rules.RuleException;
import edu.kit.iti.algover.rules.TermSelector;
import edu.kit.iti.algover.sequent.formulas.ViewFormula;
import edu.kit.iti.algover.term.Sequent;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.util.Pair;
import edu.kit.iti.algover.util.Quadruple;
import edu.kit.iti.algover.util.SubtermSelectorReplacementVisitor;
import javafx.beans.property.SimpleBooleanProperty;
import javafx.beans.property.SimpleIntegerProperty;
import javafx.collections.FXCollections;
import javafx.collections.ObservableList;
import javafx.collections.ObservableSet;
import javafx.collections.SetChangeListener;
import javafx.fxml.FXML;
import javafx.scene.control.Label;
import javafx.scene.control.ScrollPane;
import javafx.scene.input.KeyCode;
import javafx.scene.input.KeyEvent;
import javafx.scene.layout.VBox;
import org.controlsfx.control.ToggleSwitch;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

/**
 * Created by philipp on 12.07.17.
 * update by JonasKlamroth on 28.5.19
 * update by S.Grebing on 12.06.19
 *
 * This Class is the Controller for the sequent view.
 * For each part of the sequent a VBox is used to display the different formulas. Each Formula
 * is modeled by a {@link ViewFormula}. The corresponding views are {@link FormulaCell}s which are basically just
 * wrapper for {@link BasicFormulaView}.
 *
 * Styling the different formulas can be done on two levels:
 *  - via this sequent controller a style can be applied to a TermSelector
 *  - via the a BasicFormulaView directly
 * The advantage of styling in the formulaView is possibly improved performance and thus is used for
 * applications of mouseover-Style and similar. On the other Hand due to the lacking possibility of getting all
 * children of a list view (to the best of my knowledge) we provide a second possibility to apply styles directly
 * in this controller. These styles are stored in one List and thus may lead to worse performance when using to many
 * at the same time? (I think this shouldnt become a problem for reasonably large sequents.
 */
public class SequentController extends FxmlController {

    @FXML
    private ScrollPane scrollPane;

    @FXML
    private ToggleSwitch formulaLabels;

    @FXML
    private Label goalTypeLabel;
    @FXML
    private VBox antecedentBox;
    @FXML
    private VBox succedentBox;


    private ProofNodeSelector activeNode;
    private ObservableList<Quadruple<TermSelector, String, Integer, String>> styles;


    private ObservableSet<TermSelector> historyHighlightsAntec = FXCollections.observableSet();
    private ObservableSet<TermSelector> historyHighlightsSucc = FXCollections.observableSet();

    private SimpleBooleanProperty showFormulaLabels = new SimpleBooleanProperty(false);

    private SimpleIntegerProperty fontsizeProperty = new SimpleIntegerProperty(12);

    /**
     * Builds the controller and GUI for the sequent view, that is the two ListViews of
     * {@link ProofFormula}s.
     * <p>
     * This loads the GUI from the .fxml resource file
     * <tt>res/edu/kit/iti/algover/sequent/SequentView.fxml</tt>.
     *
     */
    public SequentController() {
        super("SequentView.fxml");
        PropertyManager.getInstance().currentProofStatus.addListener(((observable, oldValue, newValue) -> updateGoalTypeLabel()));

        this.styles = FXCollections.observableArrayList();

        antecedentBox.setOnKeyPressed(this::handleOnKeyPressed);
        succedentBox.setOnKeyPressed(this::handleOnKeyPressed);

        int font_size_seq_view = MainController.systemprefs.getInt("FONT_SIZE_SEQ_VIEW", 12);
        this.fontsizeProperty.setValue(font_size_seq_view);

        MainController.systemprefs.addPreferenceChangeListener(preferenceChangeEvent -> {
            int font_size_seq_view1 = preferenceChangeEvent.getNode().getInt("FONT_SIZE_SEQ_VIEW", 12);
            fontsizeProperty.set(font_size_seq_view1);
        });

/*        antecedentBox.getChildren().forEach(node -> {
            node.setOnKeyPressed(this::handleOnKeyPressed);
        });
        succedentBox.getChildren().forEach(node -> node.setOnKeyPressed(this::handleOnKeyPressed));
        /*antecedentBox.setOnKeyPressed(keyEvent -> {
            if (keyEvent.getCode() == KeyCode.ESCAPE) {
                PropertyManager.getInstance().selectedTerm.set(null);
                selectedReference.set(null);
                listener.onRemoveReferenceHighlighting();
            }
        });
        succedentBox.setOnKeyPressed(keyEvent -> {
            if (keyEvent.getCode() == KeyCode.ESCAPE) {
                PropertyManager.getInstance().selectedTerm.set(null);
                selectedReference.set(null);
                listener.onRemoveReferenceHighlighting();
            }
        });*/
        this.historyHighlightsAntec.addListener((SetChangeListener<TermSelector>) change -> {
            if(change.wasAdded()){
                addStyleForTerm(change.getElementAdded(), "referenceTarget", 25, "Target");
            } else {
                removeStyle("Target");
            }
        });
        this.historyHighlightsSucc.addListener((SetChangeListener<TermSelector>) change -> {
            if(change.wasAdded()){
                addStyleForTerm(change.getElementAdded(), "referenceTarget", 25, "Target");
            } else {
                removeStyle("Target");
            }
        });
        goalTypeLabel.setStyle("-fx-text-fill: GRAY");
        formulaLabels.selectedProperty().addListener((observable, oldValue, newValue) -> this.showFormulaLabels.set(newValue));
    }
    @FXML
    public void handleOnKeyPressed(KeyEvent event){
            if (event.getCode() == KeyCode.ESCAPE) {
                PropertyManager.getInstance().selectedTerm.set(null);
                PropertyManager.getInstance().selectedTermForReference.set(null);
            }
    }
    /**
     * Adds a style class for a certain Term.
     * @param ts A termselector pointing to the term to be styled.
     * @param styleClass The style class to be applied (has to be found int style.css
     * @param prio A priority of the Style (determines which style will be applied when styles clash)
     * @param id An id to remove the style later on.
     */
    public void addStyleForTerm(TermSelector ts, String styleClass, int prio, String id) {
        styles.add(new Quadruple<>(ts, styleClass, prio, id));
    }

    /**
     * Removes a style from the currently applied styles
     * @param id The id associated with the style to be removed (see {@link #addStyleForTerm(TermSelector, String, int, String)})
     */
    public void removeStyle(String id) {
        styles.removeIf(x -> x.fth.equals(id));
    }

    /**
     * Fills the ListViews with the formulas in the very first sequent (from the root
     * of the {@link ProofNode} tree).
     *
     * @param pvc the PVC for which to show the root sequent
     * @param proof     the existing proof or proof stub for the pvc
     */
    public void viewSequentForPVC(PVC pvc, Proof proof) {
        if (pvc != null && proof != null) {
            activeNode = new ProofNodeSelector();
            updateSequent(getActiveNode().getSequent(), null);
        }
        tryMovingOnEx();
    }

    /**
     * updates the current sequent to display the last changes to it (should be called after rule applications)
     */
    public void tryMovingOnEx() {
        if (activeNode != null) {
            try {
                ProofNode nodeBefore = activeNode.get(PropertyManager.getInstance().currentProof.get());
                while (nodeBefore.getSuccessors().size() > 0) {
                    ProofNodeSelector newActiveNode = new ProofNodeSelector(activeNode, 0);
                    ProofNode node = newActiveNode.get(PropertyManager.getInstance().currentProof.get());
                    updateSequent(node.getSequent(), null);
                    activeNode = newActiveNode;
                    nodeBefore = activeNode.get(PropertyManager.getInstance().currentProof.get());
                }
                PropertyManager.getInstance().currentProofNodeSelector.set(activeNode);
            } catch (RuleException e) {
                e.printStackTrace(); // should not happen, as long as the activeNode selector is correct
                return;
            }
            updateGoalTypeLabel();
        }
        TermSelector ts = PropertyManager.getInstance().selectedTerm.get();
        PropertyManager.getInstance().selectedTerm.setValue(null);
        PropertyManager.getInstance().selectedTerm.setValue(ts);
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
                updateSequent(activeNode.get(PropertyManager.getInstance().currentProof.get()).getSequent(), application.getBranchInfo().get(0));
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
            updateSequent(activeNode.get(PropertyManager.getInstance().currentProof.get()).getSequent(), null);
            updateGoalTypeLabel();
        } catch (RuleException e) {
            e.printStackTrace();
        }
    }

    /**
     * Displayes a given proofNode
     * @param proofNodeSelector pointing to the proofNode to be displayed
     */
    public void viewProofNode(ProofNodeSelector proofNodeSelector) {
        ProofNodeSelector selector = proofNodeSelector.getParentSelector();
        if(selector == null) {
            selector = proofNodeSelector;
        }
        selector.optionalGet(PropertyManager.getInstance().currentProof.get()).ifPresent(parentNode -> proofNodeSelector.optionalGet(PropertyManager.getInstance().currentProof.get()).ifPresent(proofNode -> {
            activeNode = proofNodeSelector;
            BranchInfo branchInfo = null;
            ProofRuleApplication application = proofNode.getProofRuleApplication();
            if (application != null && application.getBranchInfo().size() > 0) {
                branchInfo = application.getBranchInfo().get(
                        proofNodeSelector.getPath()[proofNodeSelector.getPath().length - 1]
                );
            }
            updateSequent(parentNode.getSequent(), branchInfo);
            updateGoalTypeLabel();
            if(PropertyManager.getInstance().selectedTerm.get() == null || !PropertyManager.getInstance().selectedTerm.get().isValidForSequent(parentNode.getSequent())) {
                PropertyManager.getInstance().selectedTerm.set(null);
            }
        }));
    }

    private void updateSequent(Sequent sequent, BranchInfo branchInfo) {
        antecedentBox.getChildren().setAll(calculateAssertions(sequent.getAntecedent(), TermSelector.SequentPolarity.ANTECEDENT, branchInfo));
        List<FormulaCell> after = calculateAssertions(sequent.getSuccedent(), TermSelector.SequentPolarity.SUCCEDENT, branchInfo);
        succedentBox.getChildren().setAll(after);
    }

    private List<FormulaCell> calculateAssertions(List<ProofFormula> proofFormulas, TermSelector.SequentPolarity polarity, BranchInfo branchInfo) {
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
                    formulas.add(new ViewFormula(i, term, ViewFormula.Type.CHANGED, polarity, modifiedParts, proofFormulas.get(i).getLabels()));
                    continue;
                }

                List<ProofFormula> deletions = polarity == TermSelector.SequentPolarity.ANTECEDENT
                        ? branchInfo.getDeletions().getAntecedent()
                        : branchInfo.getDeletions().getSuccedent();

                for (ProofFormula deleted : deletions) {
                    if (proofFormulas.get(i).getTerm().equals(deleted.getTerm())) {
                        formulas.add(new ViewFormula(Short.MAX_VALUE, deleted.getTerm(), ViewFormula.Type.DELETED, polarity, deleted.getLabels()));
                        deletedFormulas++;
                        continue formulaLoop;
                    }
                }
            }
            formulas.add(new ViewFormula(i, proofFormulas.get(i).getTerm(), ViewFormula.Type.ORIGINAL, polarity, proofFormulas.get(i).getLabels()));
        }

        // render additions on the sequent
        if (branchInfo != null) {
            List<ProofFormula> additions = polarity == TermSelector.SequentPolarity.ANTECEDENT
                    ? branchInfo.getAdditions().getAntecedent()
                    : branchInfo.getAdditions().getSuccedent();

            for (ProofFormula addition : additions) {
                formulas.add(new ViewFormula(formulas.size() - deletedFormulas, addition.getTerm(), ViewFormula.Type.ADDED, polarity, addition.getLabels()));
            }
        }
        return formulas.stream().map(formula -> new FormulaCell(PropertyManager.getInstance().selectedTerm, PropertyManager.getInstance().selectedTermForReference, styles, formula, showFormulaLabels, this.fontsizeProperty)).collect(Collectors.toList());

    }

    private void updateGoalTypeLabel() {
        if(PropertyManager.getInstance().currentProof.get() != null) {
            if (PropertyManager.getInstance().currentProofStatus.get() == ProofStatus.CLOSED) {
                goalTypeLabel.setText("Closed Goal");
                goalTypeLabel.setGraphic(FontAwesomeIconFactory.get().createIcon(FontAwesomeIcon.CHECK));
                goalTypeLabel.setStyle("-fx-text-fill: GREEN");
                //  Background b = new Background(new BackgroundFill(Color.rgb(22, 143, 43,0.5), null, null));
                //  antecedentBox.setBackground(b);
                //  succedentBox.setBackground(b);


            } else if(PropertyManager.getInstance().currentProofStatus.get() == ProofStatus.OPEN) {
                goalTypeLabel.setText("Open Goal");
                goalTypeLabel.setGraphic(FontAwesomeIconFactory.get().createIcon(FontAwesomeIcon.BULLSEYE));
                goalTypeLabel.setStyle("-fx-text-fill: #ff0000");
            } else if(PropertyManager.getInstance().currentProofStatus.get() == ProofStatus.CHANGED_SCRIPT) {
                goalTypeLabel.setText("Script changed");
                goalTypeLabel.setStyle("-fx-text-fill: GRAY");
                goalTypeLabel.setGraphic(null);
            } else {
                goalTypeLabel.setText("Node");
                goalTypeLabel.setStyle("-fx-text-fill: GRAY");
                goalTypeLabel.setGraphic(null);
            }
        }
    }


  /*  private Callback<ListView<ViewFormula>, ListCell<ViewFormula>> makeTermCellFactory() {
        //add highlights to style
        return listView -> new FormulaCell(selectedTerm, selectedReference, styles);
    }*/

    private ProofTermReferenceTarget attachCurrent(TermSelector selector) {
        if (activeNode != null) {
            return new ProofTermReferenceTarget(activeNode, selector);
        }
        return null;
    }

    private TermSelector termSelectorFromReference(ProofTermReferenceTarget reference) {
        if (PropertyManager.getInstance().currentProof.get() != null && reference.getProofNodeSelector() == activeNode) {
            return reference.getTermSelector();
        } else {
            return null;
        }
    }

    public void clear() {
        antecedentBox.getChildren().clear();
        succedentBox.getChildren().clear();
    }

    public ProofNode getActiveNode() {
        try {
            return activeNode.get(PropertyManager.getInstance().currentProof.get());
        } catch (RuleException e) {
            throw new RuntimeException(e);
        }
    }



    public void setActiveNode(ProofNodeSelector pns) {
        activeNode = pns;
    }

    public ProofNodeSelector getActiveNodeSelector() {
        return activeNode;
    }

    public void updateSequentController(ProofNodeSelector selector, Set<ProofTermReferenceTarget> collect) {
        this.setActiveNode(selector);
        Set<TermSelector> filteredTargets = collect.stream().map(ProofTermReferenceTarget::getTermSelector).collect(Collectors.toSet());
        this.setHistoryHighlights(FXCollections.observableSet(filteredTargets));
        this.viewProofNode(selector);


    }

    /**
     * Set the information which term to highlight for history highlighting. This method already divides the information acc. to the sequent polarity
     */
    private void setHistoryHighlights(ObservableSet<TermSelector> termsToHighlight) {
        Set<TermSelector> antec = termsToHighlight.stream().filter(termSelector -> termSelector.getPolarity() == TermSelector.SequentPolarity.ANTECEDENT).collect(Collectors.toSet());
        Set<TermSelector> succ = termsToHighlight.stream().filter(termSelector -> termSelector.getPolarity() == TermSelector.SequentPolarity.SUCCEDENT).collect(Collectors.toSet());
        this.historyHighlightsAntec.addAll(antec);
        this.historyHighlightsSucc.addAll(succ);

    }


}
