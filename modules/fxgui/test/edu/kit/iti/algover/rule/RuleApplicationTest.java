package edu.kit.iti.algover.rule;

import edu.kit.iti.algover.ApplicationTest;
import edu.kit.iti.algover.MainController;
import edu.kit.iti.algover.ProjectManagerMock;
import edu.kit.iti.algover.browser.entities.PVCEntity;
import edu.kit.iti.algover.data.BuiltinSymbols;
import edu.kit.iti.algover.parser.DafnyParserException;
import edu.kit.iti.algover.project.ProjectManager;
import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.rules.TermSelector;
import edu.kit.iti.algover.rules.impl.LetSubstitutionRule;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.term.builder.TermBuildException;
import edu.kit.iti.algover.term.parser.TermParser;
import edu.kit.iti.algover.timeline.TimelineLayout;
import edu.kit.iti.algover.util.FormatException;
import edu.kit.iti.algover.util.ProofMockUtil;
import javafx.scene.Parent;
import javafx.scene.layout.AnchorPane;
import javafx.scene.layout.Pane;
import javafx.scene.layout.StackPane;

public class RuleApplicationTest extends ApplicationTest {
    @Override
    protected Parent constructView() throws FormatException {
        ProjectManager manager = ProjectManagerMock.fromExample("gcd");
        MainController controller = new MainController(manager, SYNTAX_HIGHLIGHTING_EXECUTOR);
        controller.onClickPVCEdit(
                new PVCEntity(manager.getPVCByNameMap().get("gcd/InitInv.1"), manager.getProject().getDafnyFiles().get(0)));
        controller.onClickSequentSubterm(new TermSelector("S.0"));
        return new StackPane(controller.getView());
    }
}
