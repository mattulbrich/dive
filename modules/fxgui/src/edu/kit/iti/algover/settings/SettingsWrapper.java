package edu.kit.iti.algover.settings;

import edu.kit.iti.algover.MainController;
import edu.kit.iti.algover.project.Configuration;
import edu.kit.iti.algover.project.ProjectManager;

import java.util.prefs.Preferences;

/**
 * Wrapper Object containing all necessary information for displaying different settings.
 * If new Settings have to be added, this class needs to be extended.
 * TODO: Rafctoring such that new settings can register their objects here
 */
public class SettingsWrapper {

    private ProjectManager currentManager;

    private Configuration config;

    private Preferences systemPrefs;


    public SettingsWrapper() {
        currentManager = null;
        config = new Configuration();
        systemPrefs = MainController.systemprefs;

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
}
