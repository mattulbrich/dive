package edu.kit.iti.algover.browser;

/**
 * Created by philipp on 27.06.17.
 */
@FunctionalInterface
public interface BrowserSelectionListener {

    void onBrowserItemSelected(TreeTableEntity selectedEntity);
}
