package edu.kit.iti.algover.settings;

import edu.kit.iti.algover.project.Configuration;

public class ProjectSettingsControllerFactory implements SettingsSupplier {
    @Override
    public ISettingsController apply(Configuration configuration) {
        return new ProjectSettingsController(configuration);
    }
}
