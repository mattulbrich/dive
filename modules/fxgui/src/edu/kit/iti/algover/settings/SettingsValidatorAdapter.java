package edu.kit.iti.algover.settings;

import edu.kit.iti.algover.util.FormatException;
import edu.kit.iti.algover.util.Pair;
import edu.kit.iti.algover.util.StringValidator;

import edu.kit.iti.algover.settings.ProjectSettings.Property;
import javafx.scene.control.Control;
import org.controlsfx.validation.ValidationResult;
import org.controlsfx.validation.Validator;


import java.io.File;
import java.util.function.Supplier;

/**
 * Class providing field validators for Settings panes.
 */
public class SettingsValidatorAdapter implements Validator<String>{

    private StringValidator validator;

   // private Pair<Supplier<String>, Property> pair;
    public SettingsValidatorAdapter(StringValidator validator){
        this.validator = validator;

    }

    @Override
    public ValidationResult apply(Control control, String s) {
        try {
            validator.validate(s);
            return new ValidationResult();
        } catch (FormatException e) {
            return ValidationResult.fromError(control, e.getMessage());
        }
    }
}
