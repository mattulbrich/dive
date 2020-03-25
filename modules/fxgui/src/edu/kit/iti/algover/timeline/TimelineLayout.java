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
import javafx.beans.property.*;
import javafx.beans.value.ChangeListener;
import javafx.beans.value.ObservableValue;
import javafx.beans.value.WritableValue;
import javafx.collections.FXCollections;
import javafx.collections.ObservableList;
import javafx.geometry.Side;
import javafx.scene.Node;
import javafx.scene.input.KeyCode;
import javafx.util.Duration;
import org.controlsfx.control.HiddenSidesPane;

/**
 * Created by philipp on 10.07.17.
 * updated by Valentin on 03.03.20
 */
public class TimelineLayout extends HiddenSidesPane {

    /**
     * Design parameter form HiddenSidesPane. Same for all TimelineViews
     */
    private static final double HOVER_AREA = 20;

    // Properties. Some, if not all, of them might be moved to dedicated class.
    /**
     * Holds the items of a TimelineView
     */
    private final ListProperty<Node> nodes;
    /**
     * Representing the current position of the timeline.
     * Currently only set in this class.
     */
    private final ReadOnlyIntegerWrapper framePosition;
    private final SimpleIntegerProperty numViews;

    /**
     * The Pane that holds a SplitPane with displayed nodes. An displays
     * only two at a time.
     */
    private MultiViewSplitPane viewPane;
    private final SideArrowButton goLeft;
    private final SideArrowButton goRight;

    /**
     * Create TimelineLayout for given nodes.
     * @param nodes
     *          JavaFX Nodes. Elements of the TimelineLayout.
     */
    public TimelineLayout(Node... nodes) {
        if (nodes.length < 2) {
            throw new IllegalArgumentException("Need at least to nodes for a timeline layout");
        }

        this.numViews = new SimpleIntegerProperty(1);
        this.framePosition = new ReadOnlyIntegerWrapper(0);

        ObservableList<Node> nodeList = FXCollections.observableArrayList(nodes);
        this.nodes = new SimpleListProperty<Node>(nodeList);
        this.viewPane = new MultiViewSplitPane(nodes);

        this.goLeft = new SideArrowButton(Side.LEFT);
        this.goRight = new SideArrowButton(Side.RIGHT);
        this.numViews.bind(this.nodes.sizeProperty().subtract(1));

        this.configureGUI();
        this.configureActionHandling();
        //this.configureResizeBehaviour();

        this.updateFrame(0);
    }

    private void configureGUI() {
        this.setContent(viewPane);
        this.setLeft(goLeft);
        this.setRight(goRight);
        // Animation parameters for HiddenSidesPane.
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

                viewPane.resetDividerPositions(oldValue.intValue(), newValue.intValue());
                updateFrame(newValue.intValue());

                double target = Math.round(viewPane.getPositionOfNode(newValue.intValue()));
                viewPane.shiftProperty().unbind();
                animate(viewPane.shiftProperty(), -target);

                requestFocus();
            }
        });
        this.goLeft.setOnAction(actionEvent -> framePosition.set(framePosition.get() - 1));
        this.goRight.setOnAction(actionEvent -> framePosition.set(framePosition.get() + 1));

        // Key listening. May be moved to global Controls class
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

    /**
     * Shift the viewPane on resize.
     */
    private void configureResizeBehaviour() {
        this.widthProperty().addListener(
                (ObservableValue<? extends Number> observableValue, Number oldValue, Number newValue) -> {
                    double resizeDelta = newValue.doubleValue() - oldValue.doubleValue();
                    double viewFactor = framePosition.get() * 0.5;
                    double targetX = viewPane.shiftProperty().get() - viewFactor * resizeDelta;
                    viewPane.shiftProperty().set(targetX);
                });
    }

    /**
     * Update left and right buttons.
     * @param position
     *          New view index
     */
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

    public ReadOnlyIntegerProperty framePositionProperty() {
        return framePosition.getReadOnlyProperty();
    }

    public void setDividerPosition(double position) {
        viewPane.setDividerPositions(position);
    }

    public void addAndMoveRight(Node view) {
        nodes.add(view);
        moveFrameRight();
    }

    /**
     * Tell the TimelineView to move the frame to the right.
     * @return true iff move was possible.
     * @Deprecated Increment framePositionProperty.
     */
    @Deprecated
    public boolean moveFrameRight() {
        if (framePosition.greaterThanOrEqualTo(numViews.subtract(1)).get()) {
            return false;
        }
        framePosition.set(framePosition.get() + 1);
        return true;
    }

    /**
     * Tell the TimelineView to move the frame to the left.
     * @return true iff move was possible.
     * @Deprecated Decrement framePositionProperty.
     */
    @Deprecated
    public boolean moveFrameLeft() {
        if (framePosition.get() < 1) {
            return false;
        }

        framePosition.set(framePosition.get() - 1);
        return true;
    }


    /**
     * Start JavaFX Timeline animation
     * @param parameter
     *          parameter that should be altered and interpolated for animation.
     * @param target
     *          target value for parameter.
     * @param <T>
     *          Parameter must be a WritableValue.
     */
    private <T> void animate(WritableValue<T> parameter, T target) {
        KeyValue xkeyvalue = new KeyValue(parameter, target, Interpolator.EASE_BOTH);
        KeyFrame keyframe = new KeyFrame(Duration.millis(300), xkeyvalue);
        Timeline tl = new Timeline(keyframe);
        tl.setOnFinished(event -> {
            System.out.println("animation finished");
            this.viewPane.shiftProperty().bind(this.viewPane.positionOfNode[framePosition.get()].negate());
        });
        tl.play();
    }
}
