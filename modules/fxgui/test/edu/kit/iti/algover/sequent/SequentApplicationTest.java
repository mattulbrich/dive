package edu.kit.iti.algover.sequent;

import edu.kit.iti.algover.ApplicationTest;
import edu.kit.iti.algover.MainController;
import edu.kit.iti.algover.ProjectManagerMock;
import edu.kit.iti.algover.browser.entities.PVCEntity;
import edu.kit.iti.algover.project.ProjectManager;
import javafx.scene.Parent;
import javafx.scene.layout.StackPane;

public class SequentApplicationTest extends ApplicationTest {
    private static final String PVCID = "gcd/loop/else/Inv.2";

    @Override
    protected Parent constructView() {
        ProjectManager manager = ProjectManagerMock.fromExample("gcd");
        MainController controller = new MainController(manager, SYNTAX_HIGHLIGHTING_EXECUTOR);
        controller.onClickPVCEdit(
                new PVCEntity(manager.getProofForPVC(PVCID), manager.getPVCByNameMap().get(PVCID), manager.getProject().getDafnyFiles().get(0)));
        return new StackPane(controller.getView());
    }
}
