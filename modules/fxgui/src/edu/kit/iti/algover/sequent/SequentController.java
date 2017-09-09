package edu.kit.iti.algover.sequent;

import de.jensd.fx.glyphs.GlyphsDude;
import de.jensd.fx.glyphs.fontawesome.FontAwesomeIcon;
import edu.kit.iti.algover.project.Project;
import edu.kit.iti.algover.project.ProjectManager;
import edu.kit.iti.algover.proof.PVC;
import edu.kit.iti.algover.proof.Proof;
import edu.kit.iti.algover.proof.ProofFormula;
import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.term.Term;
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

    private final VBox upperBox;
    private final VBox lowerBox;
    private final SplitPane view;
    private final ListView<Term> antecedentView;
    private final ListView<Term> succedentView;
    private final FlowPane buttonsView;
    private final Button cancelButton;

    private Proof activeProof;
    private ProofNode activeNode;

    public SequentController(ProjectManager manager, SequentActionListener listener) {
        this.manager = manager;
        this.listener = listener;
        this.activeProof = null;

        this.cancelButton = new Button("Cancel", GlyphsDude.createIcon(FontAwesomeIcon.CLOSE));
        this.buttonsView = new FlowPane(cancelButton);
        this.antecedentView = new ListView<>();
        this.succedentView = new ListView<>();

        antecedentView.setCellFactory(this::createTermCell);
        succedentView.setCellFactory(this::createTermCell);

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
        this.lowerBox = new VBox(new Label("==>"), succedentView);
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

    private TermCell createTermCell(ListView<Term> termListView) {
        return new TermCell();
    }

    public void viewSequentForPVC(PVC pvc) {
        activeProof = manager.getProofForPVC(pvc.getName());
        activeNode = activeProof.getProofRoot();
        antecedentView.getItems().setAll(calculateAssertions(activeNode.getSequent().getAntecedent()));
        succedentView.getItems().setAll(calculateAssertions(activeNode.getSequent().getSuccedent()));
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
}
