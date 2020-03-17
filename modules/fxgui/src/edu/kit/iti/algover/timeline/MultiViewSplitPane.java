/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.timeline;


import javafx.beans.property.DoubleProperty;

import javafx.beans.value.ObservableValue;
import javafx.collections.ObservableList;
import javafx.scene.Node;
import javafx.scene.control.SplitPane;
import javafx.scene.layout.Pane;

import java.util.List;

/**
 * Created by Valentin on 03.03.2020
 * This is an encapsulation for a SplitPane. The main goal is to implement a SplitPane
 * that spans over a multiple of the application window width. It holds a certain number
 * of Nodes. Only two are visible at a time. The MultiViewSplitPane (MVSP) can be shifted to the
 * left and to the right to show any two nodes. When moving a Divider, all others are
 * moved automatically to preserve the condition, that exactly two nodes ared displayed
 * in the window.
 * One design decision is to make the MVSP not extendable. If the number of nodes in the
 * parent view changes a new MVSP must be instantiated.
 */
class MultiViewSplitPane extends Pane {

    // SplitPane that holds the displayed items
    private final SplitPane splitPane;
    // Size of MVSP relative to parent.
    private final int windowSizeMultiple;
    /**
     * every other divider has to remain in a certain global position.
     */
    private final double[] screenDividers;
    // this is dropped, once framePosition property is subscribable
    private final TimelineLayout timelineLayout;

    /**
     * Create a MVSP with given nodes.
     * @param timelineLayout
     *          Only to obtain current frame position. May be omitted in the future.
     * @param nodes
     *          Nodes to be displayed on a MVSP
     */
    public MultiViewSplitPane(TimelineLayout timelineLayout, List<Node> nodes) {
        this.timelineLayout = timelineLayout;
        this.splitPane = new SplitPane();
        this.splitPane.getItems().setAll(nodes);
        this.splitPane.prefHeightProperty().bind(this.heightProperty());
        // pad to even number
        if (nodes.size() % 2 != 0) {
            nodes.add(new Pane());
        }
        this.windowSizeMultiple = (nodes.size() / 2);
        this.screenDividers = new double[windowSizeMultiple];
        this.splitPane.prefWidthProperty().bind(this.widthProperty().multiply(windowSizeMultiple));
        dividerScreenMultiple();
        dividerAdaptionListeners();
        configureGUI();
    }

    private void configureGUI() {
        this.getChildren().add(splitPane);
    }

    private void dividerScreenMultiple() {
        ObservableList<SplitPane.Divider> dividers = this.splitPane.getDividers();
        for (int numdisp = 0; numdisp < windowSizeMultiple - 1; numdisp++) {
            screenDividers[numdisp] = (numdisp + 1) * (1.0 / windowSizeMultiple);
        }

        for (int i = 1; i < dividers.size(); i+=2) {
            resetDividerPositions(i, i);
        }
    }

    /**
     * Link divider movement.
     */
    private void dividerAdaptionListeners() {
        ObservableList<SplitPane.Divider> dividers = this.splitPane.getDividers();
        int last = 0;
        // forward
        for (int i = 0; i + 2 < dividers.size(); i+=2) {
            int boundI = i;
            dividers.get(i).positionProperty().addListener(
                    (ObservableValue<? extends Number> observableValue, Number oldValue, Number newValue) -> {
                        dividers.get(boundI + 2).setPosition(newValue.doubleValue() + (1.0 / windowSizeMultiple));
                    });
            last = i + 2;
        }

        // backward
        for (int i = last; i > 1; i -= 2) {
            int boundI = i;
            dividers.get(i).positionProperty().addListener(
                    (ObservableValue<? extends Number> observableValue, Number oldValue, Number newValue) -> {
                        dividers.get(boundI - 2).setPosition(newValue.doubleValue() - (1.0 / windowSizeMultiple));
                    });

        }
    }

    /**
     * Move every odd indexed divider to its fixed position.
     * @param oldPos
     *          Shift from frame position
     * @param newPos
     *          Shift to frame position
     */
    public void resetDividerPositions(int oldPos, int newPos) {
        if (oldPos % 2 != 1) {
            return;
        }
        double desired = screenDividers[oldPos / 2];

        ObservableList<SplitPane.Divider> dividers = splitPane.getDividers();

        double delta = (dividers.get(oldPos).getPosition() - desired);
        dividers.get(newPos).setPosition(dividers.get(newPos).getPosition() - delta);
        dividers.get(oldPos).setPosition(desired);
        splitPane.setTranslateX(splitPane.getTranslateX() + delta * splitPane.getWidth());
    }

    /**
     * Set size ratio between two displayed nodes.
     * @param pos
     *          Position between 0.0 and 1.0. Ration left node to window size
     */
    public void setDividerPositions(double pos) {
        ObservableList<SplitPane.Divider> dividers = splitPane.getDividers();
        dividers.get(0).setPosition(pos / windowSizeMultiple);
    }

    /**
     * Get the absolute position of node withe specified index
     * @param idx
     *          Index of Node in MVSP.
     * @return position of Node with index idx. -1 If index out of bounds.
     */
    public double getPositionOfNode(int idx) {
        if (idx == 0) {
            return 0;
        }
        if (idx >= splitPane.getItems().size()) {
            return -1;
        }
        return splitPane.getDividerPositions()[idx - 1] * splitPane.getWidth();
    }

    /**
     * Get property to be altered on shift.
     * @return translateXProperty of this.splitPane.
     */
    public final DoubleProperty shiftProperty() {
        return splitPane.translateXProperty();
    }
}
