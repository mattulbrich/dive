package edu.kit.iti.algover.settings;

import edu.kit.iti.algover.project.Configuration;

public class GeneralSettingsControllerFactory implements SettingsSupplier {
    @Override
    public ISettingsController apply(Configuration configuration) {
        return new GeneralSettingsController();
    }
}
