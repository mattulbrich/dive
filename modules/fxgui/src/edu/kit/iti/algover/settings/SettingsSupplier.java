package edu.kit.iti.algover.settings;

import edu.kit.iti.algover.project.Configuration;

import java.util.function.Function;

public interface SettingsSupplier extends Function<SettingsWrapper,ISettingsController> {
}
