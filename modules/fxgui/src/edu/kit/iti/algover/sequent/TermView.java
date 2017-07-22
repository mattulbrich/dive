package edu.kit.iti.algover.sequent;

import edu.kit.iti.algover.prettyprint.AnnotatedString;
import edu.kit.iti.algover.prettyprint.PrettyPrint;
import edu.kit.iti.algover.term.Term;
import javafx.scene.input.MouseEvent;
import org.fxmisc.richtext.CharacterHit;
import org.fxmisc.richtext.CodeArea;

import java.util.OptionalInt;

/**
 * Created by Philipp on 22.07.2017.
 */
public class TermView extends CodeArea {

    private final Term term;
    private final AnnotatedString str;

    public TermView(Term term) {
        super("");
        this.term = term;
        PrettyPrint p = new PrettyPrint();
        p.setPrintingFix(false);
        this.str = p.print(term, 80);

        replaceText(0, getLength(), str.toString());

        getStyleClass().add("term-view");
        setEditable(false);

        setOnMouseMoved(this::updateHighlghting);
        setOnMousePressed(this::updateHighlghting);
        setOnMouseExited(event -> clearStyle(0, getLength()));
    }

    private void updateHighlghting(MouseEvent mouseEvent) {
        CharacterHit hit = hit(mouseEvent.getX(), mouseEvent.getY());
        OptionalInt charIdx = hit.getCharacterIndex();
        if (charIdx.isPresent()) {
            AnnotatedString.TermElement elem = str.getTermElementAt(charIdx.getAsInt());
            clearStyle(0, getLength());
            setStyleClass(elem.getBegin(), elem.getEnd(), "highlighted");
            mouseEvent.consume();
        } else {
            clearStyle(0, getLength());
        }
    }
}
