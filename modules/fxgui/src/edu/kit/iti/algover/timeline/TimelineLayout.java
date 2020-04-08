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
 * updated by Valentin on 03.03.20.
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
    private final SimpleIntegerProperty framePosition;
    private final SimpleIntegerProperty numViews;

    /**
     * The Pane that holds a SplitPane with displayed nodes. An displays
     * only two at a time.
     */
    private MultiViewSplitPane viewPane;
    private final SideArrowButton goLeft;
    private final SideArrowButton goRight;

    private Timeline currentAnimation;

    /**
     * Create TimelineLayout for given nodes.
     *
     * @param nodes JavaFX Nodes. Elements of the TimelineLayout.
     */
    public TimelineLayout(Node... nodes) {
        if (nodes.length < 2) {
            throw new IllegalArgumentException("Need at least to nodes for a timeline layout");
        }
        this.numViews = new SimpleIntegerProperty(1);
        this.framePosition = new SimpleIntegerProperty(0);

        ObservableList<Node> nodeList = FXCollections.observableArrayList(nodes);
        this.nodes = new SimpleListProperty<Node>(nodeList);
        this.numViews.bind(this.nodes.sizeProperty().subtract(1));

        this.viewPane = new MultiViewSplitPane(nodes);
        this.currentAnimation = null;

        this.goLeft = new SideArrowButton(Side.LEFT);
        this.goRight = new SideArrowButton(Side.RIGHT);

        this.configureGUI();
        this.configureActionHandling();
        // Auxiliary method to set up listener on framePosition property.
        // passed as parameter. May be retrieved from state holding class in the future.
        this.configureFramePositionChangeListener(this.framePosition);

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
     * Add listener to framePosition property.
     * If the value of the specified property is changed an animation to the new
     * frame position must be triggered. The listener has to carefully handle this.
     * The {@link MultiViewSplitPane#shiftProperty()} is bound to correspond to the
     * position of the left node in the new frame position.
     * @param framePosition
     *          IntegerProperty holding the frame position.
     */
    private void configureFramePositionChangeListener(IntegerProperty framePosition) {
        framePosition.addListener((observableValue, oldValue, newValue) -> {
            // frame position set to an invalid value for display
            if (newValue.intValue() < 0 || newValue.intValue() >= numViews.get()) {
                return;
            }

            // if there is an animation, stop it.
            if (currentAnimation != null) {
                currentAnimation.stop();
                currentAnimation = null;
            }

            viewPane.resetDividerPositions(oldValue.intValue(), newValue.intValue());

            currentAnimation = createAnimation(viewPane.shiftProperty(),
                    -viewPane.nodePositionProperty(newValue.intValue()).get());

            currentAnimation.setOnFinished(event -> {
                viewPane.shiftProperty().bind(viewPane.nodePositionProperty(newValue.intValue()).negate());
            });

            viewPane.shiftProperty().unbind();
            currentAnimation.play();

            updateFrame(newValue.intValue());

            requestFocus();
        });
    }

    /**
     * Add listeners for reacting to state properties. Set Listeners for user interaction.
     */
    private void configureActionHandling() {
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
     * Update left and right buttons.
     *
     * @param position New view index
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

    private <T> Timeline createAnimation(WritableValue<T> parameter, T target) {
        KeyValue keyvalue = new KeyValue(parameter, target, Interpolator.EASE_BOTH);
        KeyFrame keyframe = new KeyFrame(Duration.millis(300), keyvalue);
        Timeline tl = new Timeline(keyframe);
        return tl;
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
     *
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
     *
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
}