/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.browser;

import edu.kit.iti.algover.browser.entities.PVCEntity;

/**
 * Created by philipp on 12.07.17.
 */
@FunctionalInterface
public interface PVCClickEditListener {
    void onEngageEntity(PVCEntity entity);
}
