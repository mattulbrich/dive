package edu.kit.iti.algover.util;

import edu.kit.iti.algover.data.BuiltinSymbols;
import edu.kit.iti.algover.data.SymbolTable;
import edu.kit.iti.algover.parser.DafnyException;
import edu.kit.iti.algover.parser.DafnyParserException;
import edu.kit.iti.algover.rules.ParameterDescription;
import edu.kit.iti.algover.rules.ParameterType;
import edu.kit.iti.algover.rules.Parameters;
import edu.kit.iti.algover.rules.ProofRule;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.term.parser.TermParser;
import javafx.application.Platform;
import javafx.geometry.Insets;
import javafx.geometry.Pos;
import javafx.scene.control.*;
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
 * Created by jklamroth on 6/12/18.
 */
public class RuleParameterDialog extends Dialog<Void> {
    private Parameters parameters = new Parameters();
    private GridPane gridPane = new GridPane();
    private TermParser termParser;

    ValidationSupport validationSupport = new ValidationSupport();

    public RuleParameterDialog(ProofRule rule, SymbolTable symbolTable) {
        this(rule, symbolTable, null);
    }

    public RuleParameterDialog(ProofRule rule, SymbolTable symbolTable, String defaultOn) {
        super();
        this.termParser = new TermParser(symbolTable);

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
            if(e.getValue().isRequired()) {
                gridPane.add(new Label(e.getKey()), 0, row);
                TextField tf = new TextField();
                if(e.getKey() == "on" && defaultOn != null) {
                    tf.setText(defaultOn);
                }
                tf.setMinWidth(200.0);
                gridPane.add(tf, 1, row);
                Platform.runLater(() -> {
                    validationSupport.registerValidator(tf, e.getValue().isRequired(), getValidatorForType(e.getValue().getType()));
                });
                row++;
            }
        }
        Button okButton = new Button("Apply");
        okButton.setMinWidth(70.0);
        okButton.setOnAction(action -> {
            setParametersFromTextFields();
            window.hide();
        });

        Button cancelButton = new Button("Cancel");
        cancelButton.setMinWidth(70.0);
        cancelButton.setOnAction(action -> {
            parameters = null;
            window.hide();
        });

        vBox.getChildren().add(gridPane);
        HBox hbox = new HBox(okButton, cancelButton);
        hbox.setAlignment(Pos.CENTER);
        hbox.setSpacing(20.0);
        vBox.getChildren().add(hbox);
        getDialogPane().setContent(vBox);

        this.setTitle("Parameters for RuleApplication");
    }

    private Validator<String> getValidatorForType(ParameterType<?> type) {
        if (type == ParameterType.TERM) {
            return this::termValidator;
        } else if (type == ParameterType.BOOLEAN) {
            return this::booleanValidator;
        }
        return null;
    }

    private void setParametersFromTextFields() {
        for (int i = 0; i < gridPane.getChildren().size() / 2; ++i) {
            TextField tf = (TextField) gridPane.getChildren().get(i * 2 + 1);
            String text = tf.getText();
            try {
                Term t = termParser.parse(text);
                parameters.putValue(((Label) (gridPane.getChildren().get(i * 2))).getText(), t);
            } catch (DafnyParserException e) {
                //e.printStackTrace();
                parameters = null;
                return;
            } catch (DafnyException e) {
                //e.printStackTrace();
                parameters = null;
                return;
            }

        }
    }

    private ValidationResult booleanValidator(Control c, String newValue) {
        if (newValue == "true" || newValue == "True") {

        }
        return new ValidationResult();
    }


    private ValidationResult termValidator(Control c, String newValue) {
        try {
            termParser.parse(newValue);
        } catch (DafnyException e) {
            return ValidationResult.fromError(c, "Could not parse this term.");
        } catch (DafnyParserException e) {
            return ValidationResult.fromError(c, "Could not parse this term.");
        }
        return new ValidationResult();
    }

    public Parameters getParameters() {
        return parameters;
    }
}
