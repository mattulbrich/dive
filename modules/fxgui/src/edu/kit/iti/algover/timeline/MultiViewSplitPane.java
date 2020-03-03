/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.timeline;

import javafx.beans.property.SimpleIntegerProperty;
import javafx.collections.ObservableList;
import javafx.scene.Node;
import javafx.scene.Parent;
import javafx.scene.control.SplitPane;
import javafx.scene.layout.Pane;

public class MultiViewSplitPane {

    private final SplitPane splitPane;

    public MultiViewSplitPane(Parent parent, Node... nodes) {
        splitPane = new SplitPane(nodes);
        parent.getChildrenUnmodifiable().addAll(splitPane);

    }

}
