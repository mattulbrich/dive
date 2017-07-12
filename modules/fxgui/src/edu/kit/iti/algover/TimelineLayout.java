package edu.kit.iti.algover;

import javafx.animation.KeyFrame;
import javafx.animation.KeyValue;
import javafx.animation.Timeline;
import javafx.beans.value.WritableValue;
import javafx.scene.Node;
import javafx.scene.SnapshotParameters;
import javafx.scene.control.SplitPane;
import javafx.scene.image.ImageView;
import javafx.scene.image.WritableImage;
import javafx.scene.layout.StackPane;
import javafx.util.Duration;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

/**
 * Created by philipp on 10.07.17.
 */
public class TimelineLayout extends StackPane {

    private final List<Node> nodes;
    private final SplitPane splitPane;

    private int framePosition = 0;

    public TimelineLayout(Node... nodes) {
        assert nodes.length >= 2;

        this.nodes = new ArrayList<>();
        this.nodes.addAll(Arrays.asList(nodes));
        this.splitPane = new SplitPane();
        getChildren().setAll(splitPane);

        updateFrame();
    }

    public void setDividerPosition(double position) {
        splitPane.setDividerPositions(position);
    }

    private void updateFrame() {
        assert framePosition < nodes.size() - 1;

        splitPane.getItems().setAll(nodes.get(framePosition), nodes.get(framePosition + 1));
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

        Node rightNode = nodes.get(framePosition+1);

        double divider = splitPane.getDividerPositions()[0];
        double rightNodeWidth = rightNode.getBoundsInParent().getWidth();

        framePosition--;
        updateFrame();

        setDividerPosition(1 - divider);

        splitPane.setTranslateX(-rightNodeWidth);
        animate(splitPane.translateXProperty(), 0);

        return true;
    }

    private <T> void animate(WritableValue<T> value, T target) {
        KeyValue xkeyvalue = new KeyValue(value, target);
        KeyFrame keyframe = new KeyFrame(Duration.millis(200), xkeyvalue);
        new Timeline(keyframe).play();
    }

}
