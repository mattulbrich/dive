/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2016 Karlsruhe Institute of Technology
 */
package de.matul.lightup;

import java.awt.Point;

public interface MovingTarget {

    Point getNorthAnchor();

    Point getSouthAnchor();

    Point getWestAnchor();

    Point getEastAnchor();

    void addListener(MovingTargetListener listener);
}
