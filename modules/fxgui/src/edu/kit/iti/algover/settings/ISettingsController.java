package edu.kit.iti.algover.settings;

import javafx.scene.Node;
import javafx.scene.layout.BorderPane;

public interface ISettingsController {
    /**
     * The name of the Node
     * @return name
     */
    public String getName();


    /**
     * Save settings after closing dialog
     */
    public abstract void save();


    /**
     *
     */
    public Node getNode();
}
