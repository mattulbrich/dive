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
import javafx.beans.property.ListProperty;
import javafx.beans.property.SimpleIntegerProperty;
import javafx.beans.property.SimpleListProperty;
import javafx.beans.value.ChangeListener;
import javafx.beans.value.ObservableValue;
import javafx.beans.value.WritableValue;
import javafx.collections.FXCollections;
import javafx.collections.ObservableList;
import javafx.geometry.Insets;
import javafx.geometry.Side;
import javafx.scene.Node;
import javafx.scene.control.SplitPane;
import javafx.scene.input.KeyCode;
import javafx.scene.layout.Pane;
import javafx.util.Duration;
import org.controlsfx.control.HiddenSidesPane;

/**
 * Created by philipp on 10.07.17.
 * updated by Valentin on 03.03.20
 */
public class TimelineLayout extends HiddenSidesPane {

    private static final double HOVER_AREA = 20;

    private final ListProperty<Node> nodes;
    private final SimpleIntegerProperty framePosition;
    private final SimpleIntegerProperty numViews;

    private final Pane contentPane;
    private final SplitPane splitPane;
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
        this.contentPane = new Pane();
        this.splitPane = new SplitPane();

        this.goLeft = new SideArrowButton(Side.LEFT);
        this.goRight = new SideArrowButton(Side.RIGHT);

        configureGUI();
        configureActionHandling();

        updateFrame(0);
    }

    /**
     * Configure gui. (Possibly divide into several methods)
     *  Hierarchy: Set content and sides (left and right) of hidden sides pane.
     *  this (HiddenSidesPane)
     *      -> contentPane (Pane)
     *          -> splitPane (SplitPane)
     *              -> nodes (SimpleListProperty of Nodes)
     *  Set default
     *  Bind dependencys on resize and divider movement.
     */
    private void configureGUI() {
        this.numViews.bind(nodes.sizeProperty().subtract(1));
        this.splitPane.getItems().setAll(this.nodes);
        this.contentPane.getChildren().setAll(this.splitPane);
        this.splitPane.prefWidthProperty().bind(
                this.contentPane.widthProperty().multiply(2));
        this.contentPane.widthProperty().addListener(new ChangeListener<>() {
            @Override
            public void changed(ObservableValue<? extends Number> observableValue, Number oldValue, Number newValue) {
                double resizeDelta = newValue.doubleValue() - oldValue.doubleValue();
                double viewFactor = (framePosition.get() * 1.0) / numViews.subtract(1).get();
                splitPane.setTranslateX(splitPane.getTranslateX() - viewFactor * resizeDelta);
            }
        });
        this.splitPane.prefHeightProperty().bind(this.contentPane.heightProperty());

        // Set default positions for dividers
        ObservableList<SplitPane.Divider> dividers = this.splitPane.getDividers();
        for (int i = 1; i < dividers.size(); i += 2) {
            dividers.get(i).setPosition((i * 1.0) / (numViews.get() - 1));
        }

        for (int i = 0; i < dividers.size(); i += 2) {
            dividers.get(i).setPosition(0.1 + ((1.0 * (i / 2)) / (numViews.get() - 1)));
        }

        // the odd numbered (even indexed) dividers depend on oneanother
        dividers.get(0).positionProperty().addListener(new ChangeListener<>() {
            @Override
            public void changed(ObservableValue<? extends Number> observableValue, Number oldValue, Number newValue) {
                dividers.get(2).setPosition(dividers.get(1).getPosition() + newValue.doubleValue());
            }
        });

        dividers.get(2).positionProperty().addListener(new ChangeListener<>() {
            @Override
            public void changed(ObservableValue<? extends Number> observableValue, Number oldValue, Number newValue) {
                dividers.get(0).setPosition(newValue.doubleValue() - dividers.get(1).getPosition());
            }
        });

        this.splitPane.setPadding(new Insets(0, 0, 0, 0));
        this.setContent(contentPane);
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

                double target = 0;
                if (newValue.intValue() > 0) {
                    target = -splitPane.getDividerPositions()[newValue.intValue() - 1] * splitPane.getWidth();
                }

                animate(splitPane.translateXProperty(),
                        target);

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

        // move second divider to the middle
        ObservableList<SplitPane.Divider> dividers = splitPane.getDividers();
        double delta = (dividers.get(1).getPosition() - 0.5);
        dividers.get(0).setPosition(dividers.get(0).getPosition() - delta);
        dividers.get(1).setPosition(0.5);
        splitPane.setTranslateX(splitPane.getTranslateX() + delta * splitPane.getWidth());

        if (position == 0) {
            goLeft.hide();
        } else {
            goLeft.show();
        }
        if (position == numViews.subtract(1).get()) {
            goRight.hide();

        } else {
            goRight.show();
        }
    }

    @Deprecated
    public void setDividerPosition(double position) {

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
