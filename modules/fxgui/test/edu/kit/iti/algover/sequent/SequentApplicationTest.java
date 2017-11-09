package edu.kit.iti.algover.sequent;

import edu.kit.iti.algover.ApplicationTest;
import edu.kit.iti.algover.ProjectManagerMock;
import edu.kit.iti.algover.browser.entities.PVCEntity;
import edu.kit.iti.algover.project.ProjectManager;
import edu.kit.iti.algover.references.ProofTermReference;
import edu.kit.iti.algover.rules.TermSelector;
import javafx.scene.Parent;
import javafx.scene.layout.StackPane;

public class SequentApplicationTest extends ApplicationTest implements SequentActionListener {
    @Override
    protected Parent constructView() {
        ProjectManager manager = ProjectManagerMock.fromExample("gcd");
        SequentController controller = new SequentController(manager, this);
        return new StackPane(controller.getView());
    }

    @Override
    public void cancelProofEditing() {

    }

    @Override
    public void considerApplication(TermSelector selector) {

    }

    @Override
    public void requestReferenceHighlighting(ProofTermReference ref) {

    }
}
