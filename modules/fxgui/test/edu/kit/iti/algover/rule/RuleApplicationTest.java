package edu.kit.iti.algover.rule;

import edu.kit.iti.algover.ApplicationTest;
import edu.kit.iti.algover.data.BuiltinSymbols;
import edu.kit.iti.algover.parser.DafnyParserException;
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

    public static void main(String[] args) {
        launch(args);
    }

    @Override
    protected Parent constructView() {
        RuleApplicationController controller = new RuleApplicationController();
        try {
            ProofNode node = ProofMockUtil.mockProofNode(null, new Term[0], new Term[] { TermParser.parse(new BuiltinSymbols(), "let f := 3 :: f == 5")});
            controller.considerApplication(node, node.getSequent(), new TermSelector("S.0"));
        } catch (TermBuildException e) {
            e.printStackTrace();
        } catch (DafnyParserException e) {
            e.printStackTrace();
        } catch (FormatException e) {
            e.printStackTrace();
        }
        StackPane pane = new StackPane(controller.getRuleApplicationView());
        return pane;
    }
}
