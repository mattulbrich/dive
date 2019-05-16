package edu.kit.iti.algover.settings;

import javafx.scene.Node;
import java.io.IOException;

public interface ISettingsController {
    /**
     * The name of the Node
     * @return name
     */
    public String getName();


    /**
     * Save settings after closing dialog. If an error occurs an  IOException is thrown
     */
    public abstract void save() throws IOException;


    /**
     * Get the graphics node
     */
    public Node getNode();
}
