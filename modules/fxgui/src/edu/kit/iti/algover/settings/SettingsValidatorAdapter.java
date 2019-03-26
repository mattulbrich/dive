package edu.kit.iti.algover.settings;

import edu.kit.iti.algover.util.StringValidators;
import javafx.scene.control.Control;
import org.controlsfx.validation.ValidationResult;
import org.controlsfx.validation.Validator;

import java.io.File;

/**
 * Class providing field validators for Settings panes.
 */
public class SettingsValidatorAdapter {

    public Validator<String> getValidatorForType() {
        return null;
    }




    private ValidationResult fileExistsValidator(Control control, StringValidators.OptionStringValidator validator, String s) {
        File file = new File(s);
        if(!file.exists()){
            return new ValidationResult();
        } else {
            return ValidationResult.fromError(control, "File already exists and will be overwritten upon saving.");
        }
    }



    private ValidationResult directoryValidator(Control control, String s) {
        File directory = new File(s);
        if(directory.isDirectory() && directory.exists()){
            return new ValidationResult();
        } else {
            return ValidationResult.fromError(control, "Path must exist and be a path.");
        }
    }

}
