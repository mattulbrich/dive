package edu.kit.iti.algover.sequent;

import de.jensd.fx.glyphs.GlyphsDude;
import de.jensd.fx.glyphs.fontawesome.FontAwesomeIcon;
import edu.kit.iti.algover.browser.entities.PVCEntity;
import edu.kit.iti.algover.project.ProjectManager;
import edu.kit.iti.algover.proof.PVC;
import edu.kit.iti.algover.proof.Proof;
import edu.kit.iti.algover.proof.ProofFormula;
import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.references.ProofTermReference;
import edu.kit.iti.algover.references.ReferenceGraph;
import edu.kit.iti.algover.rules.RuleException;
import edu.kit.iti.algover.rules.TermSelector;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.util.BindingsUtil;
import javafx.beans.property.ObjectProperty;
import javafx.beans.property.SimpleObjectProperty;
import javafx.geometry.Insets;
import javafx.geometry.Orientation;
import javafx.geometry.Pos;
import javafx.scene.control.Button;
import javafx.scene.control.Label;
import javafx.scene.control.ListView;
import javafx.scene.control.SplitPane;
import javafx.scene.layout.FlowPane;
import javafx.scene.layout.Priority;
import javafx.scene.layout.VBox;

import java.util.List;
import java.util.stream.Collectors;

/**
 * Created by philipp on 12.07.17.
 */
public class SequentController {

    private final ProjectManager manager;
    private SequentActionListener listener;

    // TODO: Extract SequentView class
    private final VBox upperBox;
    private final VBox lowerBox;
    private final SplitPane view;
    private final ListView<Term> antecedentView;
    private final ListView<Term> succedentView;
    private final FlowPane buttonsView;
    private final Button cancelButton;

    private final ObjectProperty<ProofTermReference> selectedReference;
    private final ObjectProperty<TermSelector> selectedTerm;
    private ReferenceGraph referenceGraph;
    private Proof activeProof;
    private ProofNode activeNode;

    public SequentController(ProjectManager manager, SequentActionListener listener) {
        this.manager = manager;
        this.listener = listener;
        this.activeProof = null;
        this.referenceGraph = new ReferenceGraph();
        this.selectedReference = new SimpleObjectProperty<>();
        this.selectedTerm = BindingsUtil.convert(this::termSelectorFromReference, selectedReference);

        this.cancelButton = new Button("Cancel", GlyphsDude.createIcon(FontAwesomeIcon.CLOSE));
        this.buttonsView = new FlowPane(cancelButton);
        this.antecedentView = new ListView<>();
        this.succedentView = new ListView<>();

        antecedentView.setCellFactory(termListView -> createTermCell(TermSelector.SequentPolarity.ANTECEDENT, termListView));
        succedentView.setCellFactory(termListView -> createTermCell(TermSelector.SequentPolarity.SUCCEDENT, termListView));

        this.cancelButton.setOnAction(event -> {
            if (this.listener != null) {
                this.listener.cancelProofEditing();
            }
        });

        this.buttonsView.setAlignment(Pos.TOP_RIGHT);
        this.buttonsView.setHgap(4);
        this.buttonsView.setVgap(4);
        this.buttonsView.setPadding(new Insets(10, 10, 0, 10));

        this.upperBox = new VBox(buttonsView, antecedentView);
        this.lowerBox = new VBox(new Label("|-"), succedentView);
        this.upperBox.setSpacing(10);
        this.lowerBox.setSpacing(10);
        VBox.setVgrow(upperBox, Priority.ALWAYS);
        VBox.setVgrow(lowerBox, Priority.ALWAYS);
        VBox.setVgrow(antecedentView, Priority.ALWAYS);
        VBox.setVgrow(succedentView, Priority.ALWAYS);

        this.view = new SplitPane(upperBox, lowerBox);
        view.setOrientation(Orientation.VERTICAL);
        view.setDividerPositions(0.7);
    }

    private TermCell createTermCell(TermSelector.SequentPolarity polarity, ListView<Term> termListView) {
        return new TermCell(polarity, listener, selectedTerm);
    }

    private TermSelector termSelectorFromReference(ProofTermReference reference) {
        try {
            if (reference != null && activeProof != null && reference.getProofNodeSelector().get(activeProof) == activeNode) {
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

    public void viewSequentForPVC(PVCEntity pvcEntity) {
        PVC pvc = pvcEntity.getPVC();
        if (activeProof == null || !activeProof.getPvcName().equals(pvc.getIdentifier())) {
            activeProof = manager.getProofForPVC(pvc.getIdentifier());
            activeNode = activeProof.getProofRoot();
            antecedentView.getItems().setAll(calculateAssertions(activeNode.getSequent().getAntecedent()));
            succedentView.getItems().setAll(calculateAssertions(activeNode.getSequent().getSuccedent()));
            referenceGraph = new ReferenceGraph();
            referenceGraph.addFromReferenceMap(pvcEntity.getLocation(), pvc.getReferenceMap());
        }
    }

    public void setSequentActionListener(SequentActionListener listener) {
        this.listener = listener;
    }

    private List<Term> calculateAssertions(List<ProofFormula> proofFormulas) {
        return proofFormulas.stream().map(ProofFormula::getTerm).collect(Collectors.toList());
    }

    public SplitPane getView() {
        return view;
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

    public ObjectProperty<ProofTermReference> selectedReference() {
        return selectedReference;
    }
}
