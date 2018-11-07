package edu.kit.iti.algover.rule;

import com.jfoenix.controls.JFXButton;
import de.jensd.fx.glyphs.GlyphsDude;
import de.jensd.fx.glyphs.materialicons.MaterialIcon;
import edu.kit.iti.algover.rules.*;
import edu.kit.iti.algover.term.prettyprint.PrettyPrint;
import edu.kit.iti.algover.util.RuleParameterDialog;
import javafx.css.PseudoClass;
import javafx.event.ActionEvent;
import javafx.scene.control.Label;
import javafx.scene.layout.AnchorPane;

import java.util.Map;
import java.util.logging.Logger;


public class RuleViewOverlay extends AnchorPane {

    private static final PseudoClass PC_CLOSES = PseudoClass.getPseudoClass("closes");
    private static final PseudoClass PC_SPLITTING = PseudoClass.getPseudoClass("splitting");
    private static final PseudoClass PC_NON_SPLITTING = PseudoClass.getPseudoClass("non-splitting");

    private ProofRuleApplication application;
    private TermSelector selector;

    private final Label branchCount;
    private final JFXButton applyButton;
    private final JFXButton refineButton;
    private final JFXButton applyExButton;
    private final RuleApplicationListener listener;

    public RuleViewOverlay(ProofRuleApplication application, RuleApplicationListener listener, TermSelector selector) {
        this.application = application;
        this.selector = selector;
        this.listener = listener;

        int count = application.getBranchCount();

        branchCount = new Label(count + "", GlyphsDude.createIcon(MaterialIcon.CALL_SPLIT, "20px"));
        branchCount.getStyleClass().add("branch-count");
        setPseudoClassStateFromBranches(count);

        applyButton = new JFXButton("Apply");
        applyButton.getStyleClass().add("apply");
        applyButton.setDisable(application.getApplicability() != ProofRuleApplication.Applicability.APPLICABLE);
        applyButton.setOnAction(this::onRuleApplication);

        applyExButton = new JFXButton("Apply Exh.");
        applyExButton.getStyleClass().add("applyEx");
        applyExButton.setDisable(application.getApplicability() != ProofRuleApplication.Applicability.APPLICABLE);
        applyExButton.setOnAction(actionEvent -> {
            listener.onRuleExApplication(this.application.getRule(), selector);
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
            applyButton.setDisable(this.application.getApplicability() != ProofRuleApplication.Applicability.APPLICABLE);
        });

        for (Map.Entry<String, Object> entry : application.getOpenParameters().entrySet()) {
            String parameterName = entry.getKey();
            Object value = entry.getValue();
            System.out.println(parameterName + ": " + value);
        }

        getChildren().addAll(branchCount, applyButton, refineButton, applyExButton);
        setTopAnchor(branchCount, 0.0);
        setRightAnchor(branchCount, 0.0);

        setBottomAnchor(applyButton, 0.0);
        setLeftAnchor(applyButton, 0.0);

        setTopAnchor(applyExButton, 0.0);
        setLeftAnchor(applyExButton, 0.0);

        setBottomAnchor(refineButton, 0.0);
        setRightAnchor(refineButton, 0.0);
    }

    private void onRuleApplication(ActionEvent ae) {
        if (application.getRule().getAllParameters().size() > 1 ||
                (application.getRule().getAllParameters().size() == 1 &&
                !application.getRule().getAllParameters().containsKey("on"))) {
            String on;
            try {
                PrettyPrint pp = new PrettyPrint();
                on = pp.print(selector.selectSubterm(listener.getCurrentProofNode().getSequent())).toString();
            } catch (RuleException e) {
                on = null;
            }
            RuleParameterDialog d = new RuleParameterDialog(this.application.getRule(), listener.getCurrentPVC().getAllSymbols(),
                    listener.getCurrentProofNode().getSequent(), on);
            d.showAndWait();
            if (d.getParameters() != null) {
                try {
                    application = application.getRule().makeApplication(listener.getCurrentProofNode(), d.getParameters());
                    listener.onRuleApplication(this.application);
                } catch (RuleException e) {
                    Logger.getLogger(Logger.GLOBAL_LOGGER_NAME).severe("Application of ProofRule failed with given parameters.");
                    e.printStackTrace();
                }
            } else {
                Logger.getLogger(Logger.GLOBAL_LOGGER_NAME).severe("Invalid parameters.");
            }
        } else {
            listener.onRuleApplication(this.application);
        }
    }

    private void setPseudoClassStateFromBranches(int branches) {
        switch (branches) {
            case 0:
                branchCount.pseudoClassStateChanged(PC_CLOSES, true);
                branchCount.pseudoClassStateChanged(PC_SPLITTING, false);
                branchCount.pseudoClassStateChanged(PC_NON_SPLITTING, false);
                return;
            case 1:
                branchCount.pseudoClassStateChanged(PC_CLOSES, false);
                branchCount.pseudoClassStateChanged(PC_SPLITTING, false);
                branchCount.pseudoClassStateChanged(PC_NON_SPLITTING, true);
                return;
            default:
                branchCount.pseudoClassStateChanged(PC_CLOSES, false);
                branchCount.pseudoClassStateChanged(PC_SPLITTING, true);
                branchCount.pseudoClassStateChanged(PC_NON_SPLITTING, false);
                return;
        }
    }

}
