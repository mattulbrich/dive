package edu.kit.iti.algover.rule;

import de.jensd.fx.glyphs.GlyphsDude;
import de.jensd.fx.glyphs.materialicons.MaterialIcon;
import edu.kit.iti.algover.rules.ProofRuleApplication;
import javafx.geometry.Pos;
import javafx.scene.Node;
import javafx.scene.control.Label;
import javafx.scene.layout.AnchorPane;
import javafx.scene.text.Text;
import org.controlsfx.glyphfont.Glyph;


public class RuleViewOverlay extends AnchorPane {
    private final ProofRuleApplication application;

    public RuleViewOverlay(ProofRuleApplication application) {
        this.application = application;

        int count = application.getBranchCount();

        Label branchCount = new Label(count + "", GlyphsDude.createIcon(MaterialIcon.CALL_SPLIT, "20px"));
        branchCount.setAlignment(Pos.TOP_RIGHT);
        branchCount.getStyleClass().add("branch-count");
        setRightAnchor(branchCount, 4.0);
        getChildren().add(branchCount);
    }
}
