package edu.kit.iti.algover.settings;

import edu.kit.iti.algover.project.Configuration;

public class ProjectSettingsControllerFactory implements SettingsSupplier {
    @Override
    public ISettingsController apply(SettingsWrapper settings) {
        ProjectSettingsController projectSettingsController = new ProjectSettingsController(settings.getConfig());
        projectSettingsController.setManager(settings.getCurrentManager());
        return projectSettingsController;
    }
}
