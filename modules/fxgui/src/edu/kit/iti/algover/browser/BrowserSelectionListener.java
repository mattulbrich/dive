package edu.kit.iti.algover.browser;

import edu.kit.iti.algover.browser.entities.TreeTableEntity;

/**
 * Created by philipp on 27.06.17.
 */
@FunctionalInterface
public interface BrowserSelectionListener {

    void onBrowserItemSelected(TreeTableEntity selectedEntity);
}
