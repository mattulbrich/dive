/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.timeline;

import java.util.Map;
import java.util.HashMap;
import java.util.List;
import java.util.LinkedList;

import javafx.beans.property.DoubleProperty;
import javafx.beans.property.ReadOnlyDoubleProperty;
import javafx.beans.property.ReadOnlyDoubleWrapper;
import javafx.beans.value.ChangeListener;
import javafx.beans.value.ObservableValue;
import javafx.collections.ObservableList;
import javafx.scene.Node;
import javafx.scene.control.SplitPane;
import javafx.scene.layout.Pane;
import javafx.scene.layout.Region;

/**
 * Created by Valentin on 03.03.2020
 * This is an encapsulation for a SplitPane.
 * The MultiViewSplitPane (MVSP) can be shifted to the
 * left and to the right to show exactly two items at the same time.
 * When a Divider is moved, all other divider positions are updated to preserve that condition.
 * If the number of nodes in the TimelineLayout changes a new MVSP must be instantiated.
 *
 * @author Valentin
 */
public class MultiViewSplitPane extends Pane {

    /**
     * {@link SplitPane} that holds the displayed items.
     */
    private final SplitPane splitPane;
    /**
     * Size of MVSP relative to parent.
     */
    private final int windowSizeMultiple;
    /**
     * Every odd indexed divider has to remain in a certain global position.
     */
    private final double[] screenDividers;

    /**
     * Flag for linkage of dividers of {@link MultiViewSplitPane#splitPane}.
     */
    private boolean dividersLinked = false;

    /**
     * Mapping for divider position and ChangeListeners.
     */
    private final Map<SplitPane.Divider, List<ChangeListener<? super Number>>> dividerLinking;

    /**
     * Array of properties for position of each node.
     */
    private ReadOnlyDoubleWrapper[] positionOfNode;

    /**
     * Dirty Fix: In {@link MultiViewSplitPane#resetDividerPositions(int, int)}
     * alternate divider shift direction to avoid repaint Bug in
     * {@link edu.kit.iti.algover.sequent.FormulaCell}.
     */
    private int alternateDividerShiftFactor = 1;

    /**extends
     * Create a MVSP with given nodes.
     * @param nodes
     *          Nodes to be displayed on a MVSP
     */
    public MultiViewSplitPane(final Node... nodes) {
        this.splitPane = new SplitPane();
        this.getChildren().setAll(this.splitPane);

        this.splitPane.getItems().setAll(nodes);
        // pad to even number
        if (nodes.length % 2 != 0) {
            this.splitPane.getItems().add(new Pane());
        }

        this.positionOfNode = new ReadOnlyDoubleWrapper[this.splitPane.getItems().size()];

        this.windowSizeMultiple = (this.splitPane.getItems().size() / 2);
        this.screenDividers = new double[this.windowSizeMultiple];

        this.splitPane.prefHeightProperty().bind(this.heightProperty());
        this.splitPane.prefWidthProperty().bind(this.widthProperty().multiply(this.windowSizeMultiple));

        this.positionOfNode = new ReadOnlyDoubleWrapper[this.splitPane.getItems().size()];
        this.bindNodePositions();

        this.dividerLinking = createDividerLinking();

        dividerScreenMultiple();
    }

    /**
     * Set fixed positions for odd indexed dividers of splitPane.
     */
    private void dividerScreenMultiple() {
        ObservableList<SplitPane.Divider> dividers = this.splitPane.getDividers();
        for (int numdisp = 0; numdisp < this.windowSizeMultiple - 1; numdisp++) {
            this.screenDividers[numdisp] = (numdisp + 1) * (1.0 / this.windowSizeMultiple);
        }

        for (int i = 1; i < dividers.size() - 1; i++) {
            this.resetDividerPositions(i, i + 1);
        }
    }

    /**
     * Generate {@link ChangeListener} objects that are added to the
     * {@link SplitPane.Divider#positionProperty()}
     * of dividers of {@link MultiViewSplitPane#splitPane}.
     * The listeners that are created here cause all even indexed divider to move, if one is moved.
     * @return mapping of {@link List<ChangeListener>} for each odd index divider.
     */
    private Map<SplitPane.Divider, List<ChangeListener<? super Number>>> createDividerLinking() {
        ObservableList<SplitPane.Divider> dividers = this.splitPane.getDividers();

        Map<SplitPane.Divider, List<ChangeListener<? super Number>>> mapping = new HashMap<>();

        int last = 0;
        // forward
        for (int i = 0; i + 2 < dividers.size(); i+=2) {
            int boundI = i;
            ChangeListener<Number> listener =
                    (ObservableValue<? extends Number> observableValue, Number oldValue, Number newValue) -> {
                    dividers.get(boundI + 2).setPosition(newValue.doubleValue() + (1.0 / windowSizeMultiple));
            };

            if (mapping.get(dividers.get(i)) == null) {
                mapping.put(dividers.get(i), new LinkedList<>());
            }

            mapping.get(dividers.get(i)).add(listener);

            last = i + 2;
        }

        // backward
        for (int i = last; i > 1; i -= 2) {
            int boundI = i;

            ChangeListener<Number> listener =
                    (ObservableValue<? extends Number> observableValue, Number oldValue, Number newValue) -> {
                        dividers.get(boundI - 2).setPosition(newValue.doubleValue() - (1.0 / windowSizeMultiple));
            };

            if (mapping.get(dividers.get(i)) == null) {
                mapping.put(dividers.get(i), new LinkedList<>());
            }
            mapping.get(dividers.get(i)).add(listener);
        }

        return mapping;
    }

    /**
     * Link dividers. Add specified ChangeListeners to position property of SplitPane.Divider objects
     * specified in {@link MultiViewSplitPane#dividerLinking}.
     */
    public void linkDividerPositions() {
        if (dividersLinked) {
            return;
        }
        for (SplitPane.Divider divider: dividerLinking.keySet()) {
            for (ChangeListener<? super Number> listener: dividerLinking.get(divider)) {
                divider.positionProperty().addListener(listener);
            }
        }
        dividersLinked = true;
    }

    /**
     * unlink dividers.
     */
    private void unlinkDividerPositions() {
        if (!dividersLinked) {
            return;
        }

        for (SplitPane.Divider divider: dividerLinking.keySet()) {
            for (ChangeListener<? super Number> listener: dividerLinking.get(divider)) {
                divider.positionProperty().removeListener(listener);
            }
        }

        dividersLinked = false;
    }

    /**
     * Set binding for node positions
     */
    private void bindNodePositions() {
        this.positionOfNode[0] = new ReadOnlyDoubleWrapper(0);

        for (int i = 1; i < this.positionOfNode.length; i++) {
            this.positionOfNode[i] = new ReadOnlyDoubleWrapper() {
                @Override
                public double get() {
                    return Math.round(super.get());
                }
            };
            this.positionOfNode[i].bind(this.splitPane.widthProperty().
                    multiply(this.splitPane.getDividers().get(i - 1).positionProperty()));
        }
    }

    /**
     * Return position of Node with given index in the MVSP as read-only property.
     * @param nodeIndex
     *          Index of Node in splitPane, or on MVSP, respectively.
     * @return Node position as read-only property
     */
    public ReadOnlyDoubleProperty nodePositionProperty(int nodeIndex) {
        return positionOfNode[nodeIndex];
    }
    /**
     * Move every odd indexed divider to its fixed position.
     * @param oldPos
     *          Shift from frame position
     * @param newPos
     *          Shift to frame position
     */
    public void resetDividerPositions(int oldPos, int newPos) {
        ObservableList<SplitPane.Divider> dividers = this.splitPane.getDividers();
        // Even indexed dividers are only linked upon frame change
        linkDividerPositions();

        // if the odd indexed dividers are reset
        if (oldPos % 2 == 1) {
            double desired = this.screenDividers[oldPos / 2];
            double delta = dividers.get(oldPos).getPosition() - desired;
            dividers.get(oldPos).setPosition(desired);
            dividers.get(newPos).setPosition(dividers.get(newPos).getPosition() - delta);

            alternateDividerShiftFactor *= (-1);
        }

        // A bit hacky: the divider position is required to change for ChangeListener to be triggered
        // Very hacky: not resetting it seems to prevent JavaFX repaint bug for the individual nodes.
        dividers.get(oldPos).setPosition(dividers.get(oldPos).getPosition()
                +0.01 * alternateDividerShiftFactor);

        unlinkDividerPositions();
    }

    public boolean isScreenDividerOff() {
        for (int i = 0; 2 * i + 1 < this.splitPane.getDividers().size(); i++){
            if (this.splitPane.getDividers().get(2 * i + 1).getPosition() != this.screenDividers[i]) {
                return true;
            } // else continue;
        }
        return false;
    }

    /**
     * Set size ratio between two displayed nodes.
     * @param pos
     *          Position between 0.0 and 1.0, ratio left node to window size.
     *          Position between 0.0 and 1.0, ratio left node to window size.
     */
    public void setDividerPositions(double pos) {
        ObservableList<SplitPane.Divider> dividers = this.splitPane.getDividers();
        linkDividerPositions();
        dividers.get(0).setPosition(pos / this.windowSizeMultiple);
        unlinkDividerPositions();
    }

    /**
     * Returns that property that causes to shift a MVSP. It is altered by {@link TimelineLayout}
     * on frame position change. It is even bound to the node position of the left node in display.
     * This keeps the display right during window resizing.
     * @return translateXProperty of this.splitPane
     */
    public final DoubleProperty shiftProperty() {
        return this.splitPane.translateXProperty();
    }
}
