package edu.kit.iti.algover.settings;

import javafx.scene.Node;

public interface SettingsSupplier {

    /**
     * Return the JavaFX Node  that should be displayed
     * @return
     */
    Node getNode();

    /**
     * Save settings after closing dialog
     */
    void save();

    /**
     * The name of the Node
     * @return name
     */
    String getName();
}
