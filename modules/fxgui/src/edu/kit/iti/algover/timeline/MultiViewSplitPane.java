/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.timeline;

import javafx.beans.binding.DoubleBinding;
import javafx.beans.property.DoubleProperty;

import javafx.beans.property.SimpleDoubleProperty;
import javafx.beans.value.ObservableValue;
import javafx.collections.ObservableList;
import javafx.scene.Node;
import javafx.scene.control.SplitPane;
import javafx.scene.layout.Pane;

import java.util.function.DoubleUnaryOperator;

/**
 * Created by Valentin on 03.03.2020
 * This is an encapsulation for a SplitPane.
 * The MultiViewSplitPane (MVSP) can be shifted to the
 * left and to the right to show exactly two items at the same time.
 * When a Divider is moved, all other divider positions are updated to preserve that condition.
 * If the number of nodes in the TimelineLayout changes a new MVSP must be instantiated.
 */
public class MultiViewSplitPane extends Pane {

    // SplitPane that holds the displayed items
    private final SplitPane splitPane;
    // Size of MVSP relative to parent.
    private final int windowSizeMultiple;
    /**
     * every other divider has to remain in a certain global position.
     */
    private final double[] screenDividers;
    /**
     * Create a MVSP with given nodes.
     * @param nodes
     *          Nodes to be displayed on a MVSP
     */

    public DoubleProperty[] positionOfNode;

    public MultiViewSplitPane(Node... nodes) {
        this.splitPane = new SplitPane();
        this.splitPane.prefHeightProperty().bind(this.heightProperty());

        this.splitPane.getItems().setAll(nodes);
        // pad to even number
        if (nodes.length % 2 != 0) {
            this.splitPane.getItems().add(new Pane());
        }
        this.getChildren().setAll(this.splitPane);

        this.positionOfNode = new DoubleProperty[this.splitPane.getItems().size()];

        this.windowSizeMultiple = (this.splitPane.getItems().size() / 2);
        this.screenDividers = new double[this.windowSizeMultiple];
        this.splitPane.prefWidthProperty().bind(this.widthProperty().multiply(this.windowSizeMultiple));

        this.bindNodePositions();

        // define divider behaviour
        this.dividerScreenMultiple();
        this.dividerAdaptionListeners();
    }

    private void dividerScreenMultiple() {
        ObservableList<SplitPane.Divider> dividers = this.splitPane.getDividers();
        for (int numdisp = 0; numdisp < this.windowSizeMultiple - 1; numdisp++) {
            this.screenDividers[numdisp] = (numdisp + 1) * (1.0 / this.windowSizeMultiple);
        }

        for (int i = 1; i < dividers.size(); i+=2) {
            this.resetDividerPositions(i, i);
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

    private void bindNodePositions() {
        this.positionOfNode[0] = new SimpleDoubleProperty(0);

        for (int i = 1; i < this.positionOfNode.length; i++) {
            this.positionOfNode[i] = new SimpleDoubleProperty(0);
            this.positionOfNode[i].bind(splitPane.widthProperty().multiply(splitPane.getDividerPositions()[i - 1]));
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
        double desired = this.screenDividers[oldPos / 2];

        ObservableList<SplitPane.Divider> dividers = this.splitPane.getDividers();

        double delta = (dividers.get(oldPos).getPosition() - desired);
        dividers.get(newPos).setPosition(dividers.get(newPos).getPosition() - delta);
        dividers.get(oldPos).setPosition(desired);
        double target = this.splitPane.getTranslateX() +
                delta * this.splitPane.getWidth();
        this.splitPane.setTranslateX(target);
    }

    /**
     * Set size ratio between two displayed nodes.
     * @param pos
     *          Position between 0.0 and 1.0, ratio left node to window size.
     */
    public void setDividerPositions(double pos) {
        ObservableList<SplitPane.Divider> dividers = this.splitPane.getDividers();
        dividers.get(0).setPosition(pos / this.windowSizeMultiple);
    }

    /**
     * Get the absolute position of node withe specified index
     * @param idx
     *          Index of Node in MVSP.
     * @return position of Node with index idx. -1 If index out of bounds.
     */
    public double getPositionOfNode(int idx) {
        if (idx == 0) {
            return 0.0;
        }
        if (idx >= this.splitPane.getItems().size()) {
            return -1;
        }
        return this.splitPane.getDividerPositions()[idx - 1] * this.splitPane.getWidth();
    }

    /**
     *
     * @return translateXProperty of this.splitPane.
     */
    public final DoubleProperty shiftProperty() {
        return this.splitPane.translateXProperty();
    }
}
