package edu.kit.iti.algover.browser;

import edu.kit.iti.algover.browser.entities.PVCEntity;

/**
 * Created by philipp on 12.07.17.
 */
@FunctionalInterface
public interface PVCEntityEngageListener {
    void onEngageEntity(PVCEntity entity);
}
