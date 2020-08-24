/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.rule;

import com.jfoenix.controls.JFXButton;
import de.jensd.fx.glyphs.fontawesome.utils.FontAwesomeIconFactory;
import de.jensd.fx.glyphs.materialdesignicons.MaterialDesignIcon;
import edu.kit.iti.algover.PropertyManager;
import edu.kit.iti.algover.rules.*;
import edu.kit.iti.algover.rules.ProofRuleApplication.Applicability;
import edu.kit.iti.algover.term.prettyprint.PrettyPrint;
import edu.kit.iti.algover.util.RuleParameterDialog;
import javafx.application.Platform;
import javafx.css.PseudoClass;
import javafx.scene.control.Label;
import javafx.scene.control.Tooltip;
import javafx.scene.input.MouseEvent;
import javafx.scene.layout.AnchorPane;

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
    private final RuleApplicationListener listener;

    public RuleViewOverlay(ProofRuleApplication application, RuleApplicationListener listener, TermSelector selector) {
        this.application = application;
        this.selector = selector;
        this.listener = listener;


        if(application.getApplicability()==Applicability.INSTANTIATION_REQUIRED) {
            branchCount = new Label("?", FontAwesomeIconFactory.get().createIcon(MaterialDesignIcon.CALL_SPLIT, "20px"));
            branchCount.getStyleClass().add("branch-count");
            setPseudoClassStateFromBranches(1);
            branchCount.setTooltip(new Tooltip("Instantiation required to compute number of branches"));

        } else {
            int count = application.getBranchCount();
            branchCount = new Label(count + "", FontAwesomeIconFactory.get().createIcon(MaterialDesignIcon.CALL_SPLIT, "20px"));
            branchCount.getStyleClass().add("branch-count");
            setPseudoClassStateFromBranches(count);
            branchCount.setTooltip(new Tooltip("This rule will create "+count+ " branches  when applied to selected formula"));


        }

        applyButton = new JFXButton("Apply");
        applyButton.getStyleClass().add("apply");
        applyButton.setDisable(application.getApplicability() != Applicability.APPLICABLE
                && application.getApplicability() != Applicability.INSTANTIATION_REQUIRED);
        applyButton.setOnMouseClicked(this::onRuleApplication);

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

        getChildren().addAll(branchCount, applyButton, refineButton);
        setTopAnchor(branchCount, 0.0);
        setRightAnchor(branchCount, 0.0);

        setBottomAnchor(applyButton, 0.0);
        setLeftAnchor(applyButton, 0.0);

        setBottomAnchor(refineButton, 0.0);
        setRightAnchor(refineButton, 0.0);
    }

    private void onRuleApplication(MouseEvent mouseEvent) {
        int requiredParams = 0;
        for(ParameterDescription<?> p : application.getRule().getAllParameters().values()) {
            if(p.isRequired() && p.getDefaultValue().isEmpty()) {
                requiredParams++;
            }
        }
        if (mouseEvent.isShiftDown() || (requiredParams > 0 &&
                (application.getRule().getAllParameters().size() == 1 &&
                        (!application.getRule().getAllParameters().containsValue(FocusProofRule.ON_PARAM_REQ) &&
                                !application.getRule().getAllParameters().containsValue(DefaultFocusProofRule.ON_PARAM_OPT))))) {
            String on;
            try {
                PrettyPrint pp = new PrettyPrint();
                on = pp.print(selector.selectSubterm(PropertyManager.getInstance().currentProofNode.get().getSequent())).toString();
            } catch (RuleException e) {
                on = null;
            }

            RuleParameterDialog d = new RuleParameterDialog(this.application.getRule(),
                    PropertyManager.getInstance().currentProof.get().getPVC().getSymbolTable(),
                    PropertyManager.getInstance().currentProofNode.get().getSequent(), on);
            d.setResizable(true);
            d.onShownProperty().addListener(e -> Platform.runLater(() -> d.setResizable(false)));

            d.showAndWait();
            if (d.getParameters() != null) {
                try {
                    application = application.getRule().makeApplication(PropertyManager.getInstance().currentProofNode.get(), d.getParameters());
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
        }
    }

}
