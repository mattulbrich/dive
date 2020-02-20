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
import javafx.beans.Observable;
import javafx.beans.property.SimpleIntegerProperty;
import javafx.beans.value.ChangeListener;
import javafx.beans.value.ObservableValue;
import javafx.beans.value.WritableValue;
import javafx.collections.ObservableList;
import javafx.geometry.Insets;
import javafx.scene.Node;
import javafx.scene.control.SplitPane;
import javafx.scene.input.KeyCode;
import javafx.scene.layout.Pane;
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
    private final Pane contentPane;
    private final SplitPane splitPane;
    private final GoLeftArrow goLeft;
    private final GoRightArrow goRight;


    private SimpleIntegerProperty framePosition;

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

        contentPane = new Pane();
        contentPane.getChildren().add(splitPane);

        setContent(contentPane);
        setAnimationDelay(Duration.ZERO);
        setAnimationDuration(Duration.millis(100));
        setTriggerDistance(HOVER_AREA);

        framePosition = new SimpleIntegerProperty(0);

        framePosition.addListener(new ChangeListener<Number>() {
            @Override
            public void changed(ObservableValue<? extends Number> observableValue, Number oldValue, Number newValue) {

            }
        });


        setOnKeyPressed(event -> {
            if (event.isAltDown() && event.isControlDown()) {
                if (event.getCode() == KeyCode.RIGHT) {
                    moveFrameRight();
                    event.consume();
                } else if (event.getCode() == KeyCode.LEFT) {
                    moveFrameLeft();
                    event.consume();
                } else if (event.getCode() == KeyCode.DIGIT1) {
                    framePosition.set(0);
                } else if (event.getCode() == KeyCode.DIGIT2) {
                    framePosition.set(1);
                } else if (event.getCode() == KeyCode.DIGIT3) {
                    framePosition.set(2);
                }
            }

        });
        setUpFrame();
        updateFrame();

    }

    public void setDividerPosition(double position) {
        ObservableList<SplitPane.Divider> dividers = splitPane.getDividers();

        for (int i = 0; i < dividers.size(); i++) {
            dividers.get(i).setPosition((i % 2 == 0) ? position : (1 - position));
        }
    }

    private void setUpFrame() {
        splitPane.getItems().setAll(nodes);
        splitPane.prefWidthProperty().bind(contentPane.widthProperty().multiply(2));
        splitPane.prefHeightProperty().bind(contentPane.heightProperty());
    }


    private void updateFrame() {
        assert framePosition.get() < nodes.size() - 1;

        //splitPane.getItems().setAll(nodes.get(framePosition), nodes.get(framePosition + 1));

        if (framePosition.isEqualTo(0).get()) {
            setLeft(null);
        } else {
            setLeft(goLeft);
        }
        if (framePosition.isEqualTo(nodes.size() - 2).get()) {
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

        if (framePosition.greaterThan(nodes.size() - 2).get()) {
            return false;
        }

        Node leftNode = nodes.get(framePosition.get());

        double divider = splitPane.getDividerPositions()[0];
        double leftNodeWidth = leftNode.getBoundsInParent().getWidth();

        framePosition.set(framePosition.get() + 1);
        updateFrame();

        //setDividerPosition(1 - divider);

        splitPane.setTranslateX(0);
        animate(splitPane.translateXProperty(), -2000);

        return true;
    }

    public boolean moveFrameLeft() {
        if (framePosition.get() < 1) {
            return false;
        }

        Node rightNode = nodes.get(framePosition.get() + 1);

        double divider = splitPane.getDividerPositions()[0];
        double rightNodeWidth = rightNode.getBoundsInParent().getWidth();

        framePosition.set(framePosition.get() - 1);
        updateFrame();

        //setDividerPosition(1 - divider);

        splitPane.setTranslateX(-rightNodeWidth);
        animate(splitPane.translateXProperty(), 0);

        return true;
    }


    private <T> void animate(WritableValue<T> value, T target) {
        KeyValue xkeyvalue = new KeyValue(value, target);
        KeyFrame keyframe = new KeyFrame(Duration.millis(600), xkeyvalue);
        Timeline tl = new Timeline(keyframe);
        tl.play();
        tl = null;
        System.gc();
    }
}
