/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.timeline;

import javafx.animation.Interpolator;
import javafx.animation.KeyFrame;
import javafx.animation.KeyValue;
import javafx.animation.Timeline;
import javafx.beans.property.IntegerProperty;
import javafx.beans.property.ListProperty;
import javafx.beans.property.SimpleIntegerProperty;
import javafx.beans.property.SimpleListProperty;
import javafx.beans.value.ChangeListener;
import javafx.beans.value.ObservableValue;
import javafx.beans.value.WritableValue;
import javafx.collections.FXCollections;
import javafx.collections.ObservableList;
import javafx.geometry.Side;
import javafx.scene.Node;
import javafx.scene.control.SplitPane;
import javafx.scene.input.KeyCode;
import javafx.util.Duration;
import org.controlsfx.control.HiddenSidesPane;

import java.util.Arrays;

/**
 * Created by philipp on 10.07.17.
 * updated by Valentin on 03.03.20
 */
public class TimelineLayout extends HiddenSidesPane {

    private static final double HOVER_AREA = 20;

    private final ListProperty<Node> nodes;
    private final IntegerProperty framePosition;
    private final SimpleIntegerProperty numViews;

    private final SplitPane splitPane;
    private MultiViewSplitPane viewPane;
    private final SideArrowButton goLeft;
    private final SideArrowButton goRight;

    public TimelineLayout(Node... nodes) {
        if (nodes.length < 2) {
            throw new IllegalArgumentException("Need at least to nodes for a timeline layout");
        }

        this.numViews = new SimpleIntegerProperty(1);
        this.framePosition = new SimpleIntegerProperty(0);

        // List property of all nodes in TimelineView
        ObservableList<Node> nodeList = FXCollections.observableArrayList(nodes);
        this.nodes = new SimpleListProperty<>(nodeList);

        // The content of this HiddenSidesPane is regular Pane which has a splitPane as child
        this.splitPane = new SplitPane();

        this.viewPane = new MultiViewSplitPane(this, nodes);

        this.goLeft = new SideArrowButton(Side.LEFT);
        this.goRight = new SideArrowButton(Side.RIGHT);
        this.numViews.bind(this.nodes.sizeProperty().subtract(1));

        configureGUI();
        configureActionHandling();

        updateFrame(0);
    }

    /**
     * Configure gui.
     */
    private void configureGUI() {
        this.setContent(viewPane);
        this.setLeft(goLeft);
        this.setRight(goRight);
        this.setAnimationDelay(Duration.ZERO);
        this.setAnimationDuration(Duration.millis(100));
        this.setTriggerDistance(HOVER_AREA);
    }

    /**
     * Add listeners for reacting to state properties. Set Listeners for user interaction.
     */
    private void configureActionHandling() {
        framePosition.addListener(new ChangeListener<>() {
            @Override
            public void changed(ObservableValue<? extends Number> observableValue, Number oldValue, Number newValue) {
                if (newValue.intValue() < 0 || newValue.intValue() >= numViews.get()) {
                    return;
                }
                updateFrame(newValue.intValue());

                double target = viewPane.getPositionOfNode(newValue.intValue());
                animate(viewPane.shiftProperty(), -target);

                requestFocus();
            }
        });
        this.goLeft.setOnAction(actionEvent -> framePosition.set(framePosition.get() - 1));
        this.goRight.setOnAction(actionEvent -> framePosition.set(framePosition.get() + 1));

        setOnKeyPressed(event -> {
            if (event.isAltDown()) {
                if (event.getCode() == KeyCode.RIGHT) {
                    moveFrameRight();
                    event.consume();
                } else if (event.getCode() == KeyCode.LEFT) {
                    moveFrameLeft();
                    event.consume();
                } else if (event.getCode() == KeyCode.DIGIT1) {
                    framePosition.set(0);
                    event.consume();
                } else if (event.getCode() == KeyCode.DIGIT2) {
                    framePosition.set(1);
                    event.consume();
                } else if (event.getCode() == KeyCode.DIGIT3) {
                    framePosition.set(2);
                    event.consume();
                }
            }

        });
    }

    private void updateFrame(int position) {
        assert 0 <= position && position < numViews.get();
        if (position == 0) {
            goLeft.hide();
        } else {
            goLeft.show();
        }
        if (position == numViews.get() - 1) {
            goRight.hide();

        } else {
            goRight.show();
        }
    }

    public IntegerProperty framePositionProperty() {
        return framePosition;
    }

    public void setDividerPosition(double position) {
        viewPane.setDividerPositions(position);
    }

    public void addAndMoveRight(Node view) {
        nodes.add(view);
        moveFrameRight();
    }

    @Deprecated
    public boolean moveFrameRight() {
        if (framePosition.greaterThanOrEqualTo(numViews.subtract(1)).get()) {
            return false;
        }
        framePosition.set(framePosition.get() + 1);
        return true;
    }

    @Deprecated
    public boolean moveFrameLeft() {
        if (framePosition.get() < 1) {
            return false;
        }

        framePosition.set(framePosition.get() - 1);
        return true;
    }


    private <T> void animate(WritableValue<T> value, T target) {
        KeyValue xkeyvalue = new KeyValue(value, target, Interpolator.EASE_BOTH);
        KeyFrame keyframe = new KeyFrame(Duration.millis(300), xkeyvalue);
        Timeline tl = new Timeline(keyframe);
        tl.play();
    }
}
