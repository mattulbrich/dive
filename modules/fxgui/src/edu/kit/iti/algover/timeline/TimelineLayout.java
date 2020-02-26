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
import javafx.scene.input.SwipeEvent;
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
        this.splitPane.setPadding(new Insets(0, 0, 0, 0));


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
                if (newValue.intValue() < 0 || newValue.intValue() >= nodes.length - 1) {
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
        setUpFrame();

        framePosition.set(0);
        updateFrame(0);
    }

    public void setDividerPosition(double position) {

    }

    private void setUpFrame() {

        setLeft(goLeft);
        setRight(goRight);

        splitPane.getItems().setAll(nodes);
        splitPane.prefWidthProperty().bind(contentPane.widthProperty().multiply(2));
        contentPane.widthProperty().addListener(new ChangeListener<Number>() {
            @Override
            public void changed(ObservableValue<? extends Number> observableValue, Number oldValue, Number newValue) {
                splitPane.setTranslateX(splitPane.getTranslateX() - (framePosition.get() / 2.0) * (newValue.doubleValue() - oldValue.doubleValue()));
            }
        });
        splitPane.prefHeightProperty().bind(contentPane.heightProperty());

        ObservableList<SplitPane.Divider> dividers = splitPane.getDividers();

        for (int i = 1; i < dividers.size(); i += 2) {
            dividers.get(i).setPosition((i * 1.0) / (nodes.size() - 2));
        }

        for (int i = 0; i < dividers.size(); i += 2) {
            dividers.get(i).setPosition(0.1 + ((1.0 * (i / 2)) / (nodes.size() - 2)));
        }

        dividers.get(0).positionProperty().addListener(new ChangeListener<Number>() {
            @Override
            public void changed(ObservableValue<? extends Number> observableValue, Number oldValue, Number newValue) {
                dividers.get(2).setPosition(0.5 + newValue.doubleValue());
            }
        });

        dividers.get(2).positionProperty().addListener(new ChangeListener<Number>() {
            @Override
            public void changed(ObservableValue<? extends Number> observableValue, Number oldValue, Number newValue) {
                dividers.get(0).setPosition(newValue.doubleValue() - 0.5);
            }
        });
    }

    private void updateFrame(int position) {
        assert 0 <= position && position < nodes.size() - 1;

        // move second divider to mid
        ObservableList<SplitPane.Divider> dividers = splitPane.getDividers();
        double delta = (dividers.get(1).getPosition() - 0.5);
        dividers.get(0).setPosition(dividers.get(0).getPosition() - delta);
        dividers.get(1).setPosition(0.5);
        splitPane.setTranslateX(splitPane.getTranslateX() + delta * splitPane.getWidth());

        if (position == 0) {
            goLeft.setDisable(true);
        } else {
            goLeft.setDisable(false);

        }
        if (position == nodes.size() - 2) {
            goRight.setDisable(true);

        } else {
            goRight.setDisable(false);
        }
    }

    public void addAndMoveRight(Node view) {
        nodes.add(view);
        moveFrameRight();
    }

    public boolean moveFrameRight() {
        if (framePosition.greaterThanOrEqualTo(nodes.size() - 2).get()) {
            return false;
        }
        framePosition.set(framePosition.get() + 1);
        return true;
    }

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
