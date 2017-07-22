package edu.kit.iti.algover.sequent;

import edu.kit.iti.algover.util.Span;
import javafx.beans.Observable;
import javafx.beans.property.ObjectProperty;
import javafx.beans.property.SimpleObjectProperty;
import javafx.beans.property.SimpleStringProperty;
import javafx.beans.property.StringProperty;
import javafx.beans.value.ObservableValue;
import javafx.collections.FXCollections;
import javafx.collections.ObservableList;
import javafx.geometry.Point2D;
import javafx.scene.AccessibleAttribute;
import javafx.scene.Node;
import javafx.scene.control.Label;
import javafx.scene.layout.HBox;
import javafx.scene.layout.VBox;

import java.util.ArrayList;
import java.util.List;

/**
 * Created by Philipp on 22.07.2017.
 */
public class HighlightableLabel extends VBox {

    private final StringProperty text;
    private final ObjectProperty<Span> highlightedSpan;

    public HighlightableLabel(String text) {
        this.text = new SimpleStringProperty(text);
        this.highlightedSpan = new SimpleObjectProperty<>(null);
        getChildren().setAll(new Label(text));

        this.text.addListener(this::invalidated);
        this.highlightedSpan.addListener(this::invalidated);
    }

    public int hit(double x, double y) {
        if (getHighlightedSpan() == null) {
            Label label = (Label) getChildren().get(0);
            // FIXME this throws a NullPointerException, because Labels dont support this feature
            // If i use javafx.scene.text.Text instead, this always just returns 0, I don't quite know why.
            int index = (int) label.queryAccessibleAttribute(AccessibleAttribute.OFFSET_AT_POINT, new Point2D(x, y));
            return index;
        }
        return -1;
    }

    private void invalidated(Observable observable) {
        if (getHighlightedSpan() == null) {
            getChildren().setAll(new Label(getText()));
        } else {
            setupLabelsWithHighlight();
        }
    }

    private void setupLabelsWithHighlight() {
        Span span = getHighlightedSpan();
        String[] lines = getText().split("\n");
        List<Node> nodeAccum = new ArrayList<>();
        for (int lineNum = 0; lineNum < lines.length; lineNum++) {
            if (lineNum < span.beginLine || lineNum > span.endLine) {
                nodeAccum.add(new Label(lines[lineNum]));
            } else {
                String line = lines[lineNum];
                if (span.beginLine != span.endLine) {
                    if (lineNum == span.beginLine) {
                        nodeAccum.add(new HBox(
                            new Label(line.substring(0, span.beginCharInLine - 1)),
                            highlightedLabel(line.substring(span.beginCharInLine, line.length()-1))
                        ));
                    } else if (lineNum == span.endLine) {
                        nodeAccum.add(new HBox(
                            highlightedLabel(line.substring(0, span.endCharInLine)),
                            new Label(line.substring(span.endCharInLine + 1, line.length()-1))
                        ));
                    }
                } else {
                    nodeAccum.add(new HBox(
                        new Label(line.substring(0, span.beginCharInLine - 1)),
                        highlightedLabel(line.substring(span.beginCharInLine, span.endCharInLine)),
                        new Label(line.substring(span.endCharInLine+1, line.length()-1))
                    ));
                }
            }
        }
        getChildren().setAll(nodeAccum);
    }

    private Label highlightedLabel(String text) {
        Label label = new Label(text);
        label.getStyleClass().add("highlighted");
        return label;
    }

    public void setText(String text) {
        this.text.set(text);
    }

    public String getText() {
        return text.get();
    }

    public StringProperty textProperty() {
        return text;
    }

    public Span getHighlightedSpan() {
        return highlightedSpan.get();
    }

    public ObjectProperty<Span> highlightedSpanProperty() {
        return highlightedSpan;
    }

    public void setHighlightedSpan(Span span) {
        this.highlightedSpan.set(span);
    }
}
