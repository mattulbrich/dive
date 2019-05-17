package edu.kit.iti.algover.referenceHighlighting;


/**
 * Interface for controllers that want to handle highlighting of ReferenceTargets in their corresponding views
 */
public interface ReferenceHighlightingHandler {

    /**
     * This method handles highlighting ReferenceTargets
     * @param references to highlight
     */
    void handleReferenceHighlighting(ReferenceHighlightingObject references);

}
