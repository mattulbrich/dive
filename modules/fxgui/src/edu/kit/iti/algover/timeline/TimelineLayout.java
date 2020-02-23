/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.timeline;

import javafx.animation.KeyFrame;
import javafx.animation.KeyValue;
import javafx.animation.Timeline;
import javafx.beans.value.WritableValue;
import javafx.geometry.Insets;
import javafx.scene.Node;
import javafx.scene.control.SplitPane;
import javafx.scene.input.KeyCode;
import javafx.util.Duration;
import org.controlsfx.control.HiddenSidesPane;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

/**
 * Created by philipp on 10.07.17.
 */
public class TimelineLayout extends HiddenSidesPane {

    private static final double HOVER_AREA = 20;

    private final List<Node> nodes;
    private final SplitPane splitPane;
    private final GoLeftArrow goLeft;
    private final GoRightArrow goRight;

    private int framePosition = 0;

    public TimelineLayout(Node... nodes) {
        if (nodes.length < 2) {
            throw new IllegalArgumentException("Need at least to nodes for a timeline layout");
        }

        this.nodes = new ArrayList<>();
        this.nodes.addAll(Arrays.asList(nodes));
        this.goLeft = new GoLeftArrow(this);
        this.goRight = new GoRightArrow(this);
        this.splitPane = new SplitPane();
        this.splitPane.setPadding(new Insets(0, HOVER_AREA, 0, HOVER_AREA));

        setContent(splitPane);
        setAnimationDelay(Duration.ZERO);
        setAnimationDuration(Duration.millis(100));
        setTriggerDistance(HOVER_AREA);


        setOnKeyPressed(event -> {
            if (event.isAltDown() && event.isControlDown()) {
                if (event.getCode() == KeyCode.RIGHT) {
                    moveFrameRight();
                    event.consume();
                } else if (event.getCode() == KeyCode.LEFT) {
                    moveFrameLeft();
                    event.consume();
                } else if (event.getCode() == KeyCode.DIGIT1) {
                    goToView(0);
                    event.consume();
                } else if (event.getCode() == KeyCode.DIGIT2) {
                    goToView(1);
                    event.consume();
                } else if (event.getCode() == KeyCode.DIGIT3) {
                    goToView(2);
                    event.consume();
                }
            }

        });
        updateFrame();
    }

    public void setDividerPosition(double position) {
        splitPane.setDividerPositions(position);
    }

    private void updateFrame() {
        assert framePosition < nodes.size() - 1;

        splitPane.getItems().setAll(nodes.get(framePosition), nodes.get(framePosition + 1));
        if (framePosition == 0) {
            setLeft(null);
        } else {
            setLeft(goLeft);
        }
        if (framePosition == nodes.size() - 2) {
            setRight(null);
        } else {
            setRight(goRight);
        }
        requestFocus();
    }

    public void addAndMoveRight(Node view) {
        nodes.add(view);
        moveFrameRight();
    }

    public boolean moveFrameRight() {

        if (framePosition >= nodes.size() - 2) {
            return false;
        }

        Node leftNode = nodes.get(framePosition);

        double divider = splitPane.getDividerPositions()[0];
        double leftNodeWidth = leftNode.getBoundsInParent().getWidth();

        framePosition++;
        updateFrame();

        setDividerPosition(1 - divider);

        splitPane.setTranslateX(leftNodeWidth);
        animate(splitPane.translateXProperty(), 0);

        return true;
    }

    public boolean moveFrameLeft() {
        if (framePosition < 1) {
            return false;
        }

        Node rightNode = nodes.get(framePosition + 1);

        double divider = splitPane.getDividerPositions()[0];
        double rightNodeWidth = rightNode.getBoundsInParent().getWidth();

        framePosition--;
        updateFrame();

        setDividerPosition(1 - divider);

        splitPane.setTranslateX(-rightNodeWidth);
        animate(splitPane.translateXProperty(), 0);

        return true;
    }

    /**
     * Move to specified View. Now implement as several calls to
     * move in the right direction.
     * @param viewIndex Index of target view
     * @return True if view changed.
     */
    private boolean goToView(int viewIndex) {
        int delta = viewIndex - framePosition;

        if (delta == 0) {
            return false;
        }

        if (delta > 0) { // move right
            while (delta > 0) {
                moveFrameRight();
                delta = viewIndex - framePosition;
            }
        } else {
            while (delta < 0) {
                moveFrameLeft();
                delta = viewIndex - framePosition;
            }
        }
        return true;
    }

    private <T> void animate(WritableValue<T> value, T target) {
        KeyValue xkeyvalue = new KeyValue(value, target);
        KeyFrame keyframe = new KeyFrame(Duration.millis(200), xkeyvalue);
        Timeline tl = new Timeline(keyframe);
        tl.play();
    }
}
