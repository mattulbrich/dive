package edu.kit.iti.algover.settings;

import javafx.scene.Node;

public interface SettingsSupplier {

    //returns Node
    public Node getNode();

    //save settings after closing dialog
    public void save();
}
