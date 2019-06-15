package edu.kit.iti.algover.settings;

import java.util.prefs.Preferences;

public interface GeneralSettingsHandler {

    void onGeneralSettingsChanged(Preferences systemPrefs);
}
