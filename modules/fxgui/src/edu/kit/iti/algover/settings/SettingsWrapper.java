/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.settings;

import edu.kit.iti.algover.Lookup;
import edu.kit.iti.algover.MainController;
import edu.kit.iti.algover.project.Configuration;
import edu.kit.iti.algover.project.ProjectManager;

import java.util.prefs.Preferences;

/**
 * Wrapper Object containing all necessary information for displaying different settings.
 * If new Settings have to be added, this class needs to be extended.
 * TODO: Rafactoring use lookup
 */
public class SettingsWrapper {

    private ProjectManager currentManager;

    private Configuration config;

    private Preferences systemPrefs;

    private Lookup lookup;



    public SettingsWrapper() {
        currentManager = null;
        config = new Configuration();
        systemPrefs = MainController.systemprefs;
        lookup = null;

    }

    public ProjectManager getCurrentManager() {
        return currentManager;
    }

    public void setCurrentManager(ProjectManager currentManager) {
        this.currentManager = currentManager;
    }

    public Configuration getConfig() {
        return config;
    }

    public void setConfig(Configuration config) {
        this.config = config;
    }

    public Preferences getSystemPrefs() {
        return systemPrefs;
    }

    public void setSystemPrefs(Preferences systemPrefs) {
        this.systemPrefs = systemPrefs;
    }

    public Lookup getLookup() {
        return lookup;
    }

    public void setLookup(Lookup lookup) {
        this.lookup = lookup;
    }
}
