package edu.kit.iti.algover.rule.script;

import edu.kit.iti.algover.script.ast.Position;
import javafx.beans.property.SimpleListProperty;
import javafx.beans.property.SimpleStringProperty;
import javafx.beans.value.ObservableValue;
import javafx.collections.FXCollections;
import javafx.collections.ObservableList;
import javafx.geometry.Insets;
import javafx.scene.Node;
import javafx.scene.control.Label;
import javafx.scene.input.MouseButton;
import javafx.scene.layout.Background;
import javafx.scene.layout.BackgroundFill;
import javafx.scene.paint.Color;
import javafx.scene.paint.Paint;
import javafx.scene.text.Font;
import javafx.scene.text.FontPosture;
import org.fxmisc.richtext.CodeArea;
import org.reactfx.collection.LiveList;
import org.reactfx.value.Val;

import java.util.function.IntFunction;

/**
 * Factory for the gutter in the script view
 * @author A.Weigl (PSDBG)
 * @author S. Grebing (adapted)
 */
public class GutterFactory implements IntFunction<Node> {

    /**
     * Background Color
     */
    private final Background defaultBackground =
            new Background(new BackgroundFill(Color.web("#ddd"), null, null));

    private final Val<Integer> nParagraphs;

    private Insets defaultInsets = new Insets(0.0, 5.0, 0.0, 5.0);

    private Paint defaultTextFill = Color.web("#666");

    private Font defaultFont = Font.font("monospace", FontPosture.ITALIC, 13);

    private ObservableList<GutterAnnotation> lineAnnotations =
            new SimpleListProperty<>(FXCollections.observableArrayList());


    public GutterFactory(CodeArea codeArea) {
        nParagraphs = LiveList.sizeOf(codeArea.getParagraphs());
        for (int i = 0; i < 100; i++) {
            lineAnnotations.add(new GutterAnnotation());
        }

        // Update the gutter.
        // If a line is deleted, delete also the image entry for this line
        nParagraphs.addInvalidationObserver((n) -> {
            int diff = lineAnnotations.size() - n;
            if (diff > 0) {
                lineAnnotations.remove(n, lineAnnotations.size());
            }
        });


    }

    @Override
    public Node apply(int idx) {
        if (idx == -1) return new Label("idx is -1!"); //TODO weigl debug
        Val<String> formatted = nParagraphs.map(n -> format(idx + 1, n));
        GutterAnnotation model = getLineAnnotation(idx);
        model.setLineNumber(idx);
        GutterView hbox = new GutterView(model);
        model.textProperty().bind(formatted);



//TODO Action goes here
        hbox.setOnMouseClicked((mevent) -> {
            mevent.consume();
            if (mevent.getButton() == MouseButton.PRIMARY)
                System.out.println("mevent = " + mevent);
        });

        hbox.getLineNumber().setFont(defaultFont);
        hbox.setBackground(defaultBackground);
        hbox.getLineNumber().setTextFill(defaultTextFill);
        hbox.setPadding(defaultInsets);
        hbox.getStyleClass().add("lineno");
        hbox.setStyle("-fx-cursor: hand");
        return hbox;
    }

    private String format(int x, int max) {
        int digits = (int) Math.floor(Math.log10(max)) + 1;
        return String.format("%" + digits + "d", x);
    }

    public GutterAnnotation getLineAnnotation(int idx) {
        if (lineAnnotations.size() <= idx) {
            for (int i = lineAnnotations.size(); i < idx + 1; i++) {
                lineAnnotations.add(new GutterAnnotation());
            }
        }
        return lineAnnotations.get(idx);
    }

    public ObservableList<GutterAnnotation> getAnnotations() {
        return this.lineAnnotations;
    }
}
