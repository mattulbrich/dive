package edu.kit.iti.algover.rule;

import com.jfoenix.controls.JFXButton;
import de.jensd.fx.glyphs.GlyphsDude;
import de.jensd.fx.glyphs.materialicons.MaterialIcon;
import edu.kit.iti.algover.rules.ProofRuleApplication;
import edu.kit.iti.algover.rules.RuleException;
import javafx.scene.control.Label;
import javafx.scene.layout.AnchorPane;


public class RuleViewOverlay extends AnchorPane {

    private ProofRuleApplication application;

    private final Label branchCount;
    private final JFXButton applyButton;
    private final JFXButton refineButton;
    private final RuleApplicationListener listener;

    public RuleViewOverlay(ProofRuleApplication application, RuleApplicationListener listener) {
        this.application = application;
        this.listener = listener;

        int count = application.getBranchCount();

        branchCount = new Label(count + "", GlyphsDude.createIcon(MaterialIcon.CALL_SPLIT, "20px"));
        branchCount.getStyleClass().add("branch-count");

        applyButton = new JFXButton("Apply");
        applyButton.getStyleClass().add("apply");
        applyButton.setDisable(application.getApplicability() == ProofRuleApplication.Applicability.NOT_APPLICABLE);

        applyButton.setOnAction(actionEvent -> {
            listener.onRuleApplication(this.application);
        });

        refineButton = new JFXButton("Refine");
        refineButton.getStyleClass().add("refine");
        refineButton.setDisable(!application.isRefinable());
        refineButton.setOnAction(actionEvent -> {
            try {
                this.application = application.refine();
            } catch (RuleException e) {
                e.printStackTrace();
            }
        });

        getChildren().addAll(branchCount, applyButton, refineButton);
        setTopAnchor(branchCount, 0.0);
        setRightAnchor(branchCount, 0.0);

        setBottomAnchor(applyButton, 0.0);
        setLeftAnchor(applyButton, 0.0);

        setBottomAnchor(refineButton, 0.0);
        setRightAnchor(refineButton, 0.0);
    }
}
