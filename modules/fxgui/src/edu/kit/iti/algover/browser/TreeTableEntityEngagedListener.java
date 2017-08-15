package edu.kit.iti.algover.browser;

import edu.kit.iti.algover.browser.entities.TreeTableEntity;

/**
 * Created by philipp on 12.07.17.
 */
@FunctionalInterface
public interface TreeTableEntityEngagedListener {
    void onDoubleClickTreeEntity(TreeTableEntity entity);
}
