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

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

class MultiViewSplitPane extends Pane {

    private final SplitPane splitPane;
    private final int windowSizeMultiple;
    /**
     * every other divider has to remain in a certain global position.
     */
    private final double[] screenDividers;
    // this is dropped, once framePosition property is subscribable
    private final TimelineLayout timelineLayout;


    public MultiViewSplitPane(TimelineLayout timelineLayout, Node... nodes) {
        this.timelineLayout = timelineLayout;
        this.splitPane = new SplitPane();
        this.getChildren().setAll(splitPane);
        this.splitPane.prefHeightProperty().bind(this.heightProperty());
        List<Node> pnodes = new ArrayList<Node>();
        pnodes.addAll(Arrays.asList(nodes));
        if (pnodes.size() % 2 != 0) {
            pnodes.add(new Pane());
            System.out.println("Pane added");
        }
        this.splitPane.getItems().setAll(pnodes);
        this.windowSizeMultiple = (pnodes.size() / 2);
        this.screenDividers = new double[windowSizeMultiple];
        this.splitPane.prefWidthProperty().bind(this.widthProperty().multiply(windowSizeMultiple));
        dividerScreenMultiple();
        dividerAdaptionListeners();
    }

    private void dividerScreenMultiple() {
        ObservableList<SplitPane.Divider> dividers = this.splitPane.getDividers();
        for (int numdisp = 0; numdisp < windowSizeMultiple - 1; numdisp++) {
            screenDividers[numdisp] = (numdisp + 1) * (1.0 / windowSizeMultiple);
        }

        dividers.get(0).setPosition(0.2 / windowSizeMultiple);
        dividers.get(dividers.size() - 1).setPosition(screenDividers[screenDividers.length - 1] + (0.2 / windowSizeMultiple));

        int numdisp = 0;
        for (int i = 1; i < dividers.size(); i+=2) {
            dividers.get(i).setPosition(screenDividers[numdisp++]);
        }
    }

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

        this.widthProperty().addListener(
                (ObservableValue<? extends Number> observableValue, Number oldValue, Number newValue) -> {
                    double resizeDelta = newValue.doubleValue() - oldValue.doubleValue();
                    double viewFactor = (timelineLayout.framePositionProperty().get() * 1.0) /
                            (splitPane.getItems().size() - 2);
                    splitPane.setTranslateX(splitPane.getTranslateX() - viewFactor * resizeDelta);
                });
    }

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

    public void setDividerPositions(double pos) {
        ObservableList<SplitPane.Divider> dividers = splitPane.getDividers();
        dividers.get(0).setPosition(pos / windowSizeMultiple);
    }

    public double getPositionOfNode(int idx) {
        if (idx == 0) {
            return 0;
        }
        if (idx >= splitPane.getItems().size()) {
            return -1;
        }
        return splitPane.getDividerPositions()[idx - 1] * splitPane.getWidth();
    }

    public final DoubleProperty shiftProperty() {
        return splitPane.translateXProperty();
    }
}
