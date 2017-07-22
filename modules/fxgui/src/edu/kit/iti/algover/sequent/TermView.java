package edu.kit.iti.algover.sequent;

import edu.kit.iti.algover.prettyprint.AnnotatedString;
import edu.kit.iti.algover.prettyprint.PrettyPrint;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.util.Span;
import javafx.scene.control.Label;
import javafx.scene.input.MouseEvent;

/**
 * Created by Philipp on 22.07.2017.
 */
public class TermView extends HighlightableLabel {

    private final Term term;

    public TermView(Term term) {
        super("");
        this.term = term;
        getStyleClass().add("term-view");
        updateText(term);
        setOnMouseClicked(this::handleClick);
    }

    private void handleClick(MouseEvent mouseEvent) {
        System.out.println(hit(mouseEvent.getX(), mouseEvent.getY()));
    }

    private void updateText(Term term) {
        PrettyPrint p = new PrettyPrint();
        p.setPrintingFix(false);
        AnnotatedString prettyPrinted = p.print(term, 10);
        setText(prettyPrinted.toString());
        //setHighlightedSpan(new Span(1, 2, 4, 6));
    }
}
