package edu.kit.iti.algover.sequent;

import edu.kit.iti.algover.project.Project;
import edu.kit.iti.algover.proof.PVC;
import edu.kit.iti.algover.proof.ProofFormula;
import edu.kit.iti.algover.term.Sequent;
import javafx.beans.property.ObjectProperty;
import javafx.beans.property.SimpleObjectProperty;
import javafx.scene.Node;
import javafx.scene.control.ListView;

import java.util.List;
import java.util.stream.Collectors;

/**
 * Created by philipp on 12.07.17.
 */
public class SequentController {

    private final Project project;
    private final ListView<SequentAssertion> view;

    private Sequent activeSequent;

    public SequentController(Project project) {
        this.project = project;
        this.view = new ListView<>();
        this.activeSequent = null;
    }

    public void viewSequentForPVC(PVC pvc) {
        activeSequent = pvc.getSequent();
        view.getItems().setAll(calculateAssertions(activeSequent.getAntecedent()));
    }

    private List<SequentAssertion> calculateAssertions(List<ProofFormula> antecedent) {
        return antecedent.stream().map(SequentAssertion::new).collect(Collectors.toList());
    }

    public ListView<SequentAssertion> getView() {
        return view;
    }
}
