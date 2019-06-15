/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.settings;

import edu.kit.iti.algover.project.Configuration;

public class GeneralSettingsControllerFactory implements SettingsSupplier {
    @Override
    public ISettingsController apply(SettingsWrapper settings) {
        return new GeneralSettingsController(settings.getSystemPrefs());
    }
}
