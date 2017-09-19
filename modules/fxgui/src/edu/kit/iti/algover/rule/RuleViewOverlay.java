package edu.kit.iti.algover.rule;

import com.jfoenix.controls.JFXButton;
import de.jensd.fx.glyphs.GlyphsDude;
import de.jensd.fx.glyphs.materialicons.MaterialIcon;
import edu.kit.iti.algover.rules.ProofRuleApplication;
import javafx.geometry.Pos;
import javafx.scene.Node;
import javafx.scene.control.Button;
import javafx.scene.control.Label;
import javafx.scene.layout.AnchorPane;
import javafx.scene.paint.Paint;
import javafx.scene.text.Text;
import org.controlsfx.glyphfont.Glyph;


public class RuleViewOverlay extends AnchorPane {
    private final ProofRuleApplication application;

    private final Label branchCount;
    private final JFXButton applyButton;
    private final JFXButton refineButton;

    public RuleViewOverlay(ProofRuleApplication application) {
        this.application = application;

        int count = application.getBranchCount();

        branchCount = new Label(count + "", GlyphsDude.createIcon(MaterialIcon.CALL_SPLIT, "20px"));
        branchCount.getStyleClass().add("branch-count");

        applyButton = new JFXButton("Apply");
        applyButton.getStyleClass().add("apply");
        applyButton.setDisable(application.getApplicability() != ProofRuleApplication.Applicability.NOT_APPLICABLE);

        applyButton.setOnAction(actionEvent -> {
            application.getBranchInfo().forEach(branchInfo -> {
                System.out.println("Additions: " + branchInfo.getAdditions());
                System.out.println("Deletions: " + branchInfo.getDeletions());
                System.out.println("Modifications: " + branchInfo.getReplacements());
            });
        });

        refineButton = new JFXButton("Refine");
        refineButton.getStyleClass().add("refine");
        refineButton.setDisable(!application.isRefinable());

        getChildren().addAll(branchCount, applyButton, refineButton);
        setTopAnchor(branchCount, 0.0);
        setRightAnchor(branchCount, 0.0);

        setBottomAnchor(applyButton, 0.0);
        setLeftAnchor(applyButton, 0.0);

        setBottomAnchor(refineButton, 0.0);
        setRightAnchor(refineButton, 0.0);
    }
}
