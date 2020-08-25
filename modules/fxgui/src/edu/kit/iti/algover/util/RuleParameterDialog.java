/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.util;

import edu.kit.iti.algover.data.BuiltinSymbols;
import edu.kit.iti.algover.data.SymbolTable;
import edu.kit.iti.algover.parser.DafnyException;
import edu.kit.iti.algover.parser.DafnyParserException;
import edu.kit.iti.algover.rules.ParameterDescription;
import edu.kit.iti.algover.rules.ParameterType;
import edu.kit.iti.algover.rules.Parameters;
import edu.kit.iti.algover.rules.ProofRule;
import edu.kit.iti.algover.rules.TermParameter;
import edu.kit.iti.algover.term.Sequent;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.term.parser.TermParser;
import javafx.application.Platform;
import javafx.geometry.Insets;
import javafx.geometry.Pos;
import javafx.scene.control.*;
import javafx.scene.input.KeyCode;
import javafx.scene.input.KeyCodeCombination;
import javafx.scene.input.KeyCombination;
import javafx.scene.layout.ColumnConstraints;
import javafx.scene.layout.GridPane;
import javafx.scene.layout.HBox;
import javafx.scene.layout.VBox;
import javafx.stage.Window;
import org.controlsfx.validation.ValidationResult;
import org.controlsfx.validation.ValidationSupport;
import org.controlsfx.validation.Validator;
import java.util.Map;

/**
 * This Dialog allows for entering values for parameters of rule applications.
 * @author Jonas Klamroth (06/2018)
 */
public class RuleParameterDialog extends Dialog<Void> {
    private Parameters parameters = new Parameters();
    private GridPane gridPane = new GridPane();
    private ProofRule rule;
    private final Sequent sequent;
    private TermParser termParser;
    private Parameters expectedParameters;

    ValidationSupport validationSupport = new ValidationSupport();

    public RuleParameterDialog(ProofRule rule, SymbolTable symbolTable, Sequent sequent) {
        this(rule, symbolTable, sequent, null);
    }

    public RuleParameterDialog(ProofRule rule, SymbolTable symbolTable, Sequent sequent, String defaultOn) {
        this.rule = rule;
        this.sequent = sequent;
        this.termParser = new TermParser(symbolTable);
        this.termParser.setSchemaMode(true);

        Window window = this.getDialogPane().getScene().getWindow();
        window.setOnCloseRequest(event -> {
            parameters = null;
            window.hide();
        });

        VBox vBox = new VBox();
        vBox.setPadding(new Insets(10, 10, 10, 10));
        vBox.setSpacing(10);
        vBox.getChildren().add(new Label("Please insert the requested parameters to apply the rule."));

        ColumnConstraints col1 = new ColumnConstraints();
        col1.setPercentWidth(25);
        gridPane.getColumnConstraints().add(col1);

        int row = 0;
        gridPane.setVgap(10);
        for (Map.Entry<String, ParameterDescription<?>> e : rule.getAllParameters().entrySet()) {
            gridPane.add(new Label(e.getKey()), 0, row);
            TextField tf = new TextField();
            tf.setUserData(e.getValue().getType());
            if(e.getKey().equals("on") && defaultOn != null) {
                tf.setText(defaultOn);
            }
            tf.setMinWidth(200.0);
            gridPane.add(tf, 1, row);
            Platform.runLater(() -> validationSupport.registerValidator(tf, e.getValue().isRequired(),
                    getValidatorForType(e.getValue().getType())));
            row++;
        }
        Button okButton = new Button("Apply");
        okButton.setMinWidth(70.0);
        okButton.setOnAction(action -> {
            setParametersFromTextFields();
            window.hide();
        });
        okButton.sceneProperty().addListener((observable, oldValue, newScene) -> {
            if (newScene != null) {
                newScene.getAccelerators().put(
                        new KeyCodeCombination(KeyCode.ENTER),
                        okButton::fire
                );
            }
        });

        Button cancelButton = new Button("Cancel");
        cancelButton.setMinWidth(70.0);
        cancelButton.setOnAction(action -> {
            parameters = null;
            window.hide();
        });
        cancelButton.sceneProperty().addListener((observable, oldValue, newScene) -> {
            if (newScene != null) {
                newScene.getAccelerators().put(
                        new KeyCodeCombination(KeyCode.ESCAPE),
                        cancelButton::fire
                );
            }
        });

        vBox.getChildren().add(gridPane);
        HBox hbox = new HBox(okButton, cancelButton);
        hbox.setAlignment(Pos.CENTER);
        hbox.setSpacing(20.0);
        vBox.getChildren().add(hbox);
        getDialogPane().setContent(vBox);

        this.setTitle("Parameters for RuleApplication");
        this.setResizable(true);
        //workaround GTK based desktops
        this.onShownProperty().addListener( e-> Platform.runLater(() -> this.setResizable(true)));
    }

    private Validator<String> getValidatorForType(ParameterType<?> type) {
        if (type == ParameterType.TERM) {
            return this::termValidator;
        } else if (type == ParameterType.BOOLEAN) {
            return this::booleanValidator;
        } else if (type == ParameterType.STRING) {
            return this::stringValidator;
        }
        return null;
    }

    // REVIEW MU: These catches are likely to become trouble.
    private void setParametersFromTextFields() {
        for (int i = 0; i < gridPane.getChildren().size() / 2; ++i) {
            TextField tf = (TextField) gridPane.getChildren().get(i * 2 + 1);
            String text = tf.getText();
            String label = ((Label) (gridPane.getChildren().get(i * 2))).getText();
            ParameterDescription<?> pd = rule.getAllParameters().get(label);
            if(tf.getUserData().equals(ParameterType.TERM)) {
                try {
                    Term t = termParser.parse(text);
                    parameters.checkAndPutValue(pd, new TermParameter(t, sequent));
                    //parameters.putValue(((Label) (gridPane.getChildren().get(i * 2))).getText(), new TermParameter(t, sequent));
                } catch (DafnyParserException | DafnyException e) {
                    //e.printStackTrace();
                    parameters = null;
                    return;
                }
            } else if(tf.getUserData().equals(ParameterType.STRING)) {
                parameters.checkAndPutValue(pd, text);
                //parameters.putValue(((Label) (gridPane.getChildren().get(i * 2))).getText(), text);
            } else if(tf.getUserData().equals(ParameterType.BOOLEAN)) {
                boolean b = Boolean.parseBoolean(text);
                parameters.checkAndPutValue(pd, b);
            } else {
                throw new RuntimeException("ParameterType " + tf.getUserData() + " is unkown.");
            }

        }
    }

    private ValidationResult booleanValidator(Control c, String newValue) {
        if (newValue.equalsIgnoreCase("true")
                || newValue.equalsIgnoreCase("false")) {
            return new ValidationResult();
        }
        return ValidationResult.fromError(c, "Boolean values must be true or false.");
    }

    private ValidationResult stringValidator(Control c, String newValue) {
        return new ValidationResult();
    }


    private ValidationResult termValidator(Control c, String newValue) {
        try {
            termParser.parse(newValue);
        } catch (DafnyException | DafnyParserException e) {
            return ValidationResult.fromError(c, "Could not parse this term.");
        }
        return new ValidationResult();
    }

    public Parameters getParameters() {
        return parameters;
    }
}
