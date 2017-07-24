package edu.kit.iti.algover.sequent;

import edu.kit.iti.algover.project.Project;
import edu.kit.iti.algover.proof.PVC;
import edu.kit.iti.algover.proof.ProofFormula;
import edu.kit.iti.algover.term.Sequent;
import edu.kit.iti.algover.term.Term;
import javafx.geometry.Orientation;
import javafx.scene.Node;
import javafx.scene.control.Label;
import javafx.scene.control.ListView;
import javafx.scene.control.SplitPane;
import javafx.scene.layout.HBox;
import javafx.scene.layout.Priority;
import javafx.scene.layout.VBox;

import java.util.List;
import java.util.stream.Collectors;

/**
 * Created by philipp on 12.07.17.
 */
public class SequentController {

    private final Project project;
    private final VBox viewSequent;
    private final SplitPane view;
    private final ListView<Term> antecedentView;
    private final ListView<Term> succedentView;
    private final ScriptView scriptView;

    private Sequent activeSequent;

    public SequentController(Project project) {
        this.project = project;
        this.antecedentView = new ListView<>();
        this.succedentView = new ListView<>();
        this.scriptView = new ScriptView();
        this.activeSequent = null;

        antecedentView.setCellFactory(this::createTermCell);
        succedentView.setCellFactory(this::createTermCell);

        this.viewSequent = new VBox(antecedentView, new Label("==>"), succedentView);
        this.view = new SplitPane(viewSequent, scriptView);
        view.setOrientation(Orientation.VERTICAL);
        view.setDividerPositions(0.7);
    }

    private TermCell createTermCell(ListView<Term> termListView) {
        return new TermCell();
    }

    public void viewSequentForPVC(PVC pvc) {
        activeSequent = pvc.getSequent();
        antecedentView.getItems().setAll(calculateAssertions(activeSequent.getAntecedent()));
        succedentView.getItems().setAll(calculateAssertions(activeSequent.getSuccedent()));
    }

    private List<Term> calculateAssertions(List<ProofFormula> proofFormulas) {
        return proofFormulas.stream().map(ProofFormula::getTerm).collect(Collectors.toList());
    }

    public SplitPane getView() {
        return view;
    }
}
