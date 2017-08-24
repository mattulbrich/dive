/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.sequent;

import edu.kit.iti.algover.rules.SubtermSelector;
import edu.kit.iti.algover.term.prettyprint.AnnotatedString;
import edu.kit.iti.algover.term.prettyprint.PrettyPrint;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.util.TextUtil;
import javafx.geometry.Bounds;
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
    private final TermViewListener listener;

    public TermView(Term term, TermViewListener listener) {
        super("");
        getStyleClass().add("term-view");

        this.term = term;
        this.listener = listener;
        PrettyPrint p = new PrettyPrint();
        this.str = p.print(term, 40);
        setFocusTraversable(false);

        String prettyPrinted = str.toString();

        // This is a hack, but it seems to be impossible without it...
        Bounds bounds = TextUtil.computeTextBounds(prettyPrinted, getStyleClass(), getStylesheets());

        replaceText(0, getLength(), prettyPrinted);

        setEditable(false);

        final double safetyPadding = 1.1; // 10%, this is such a hack ... :(
        double neededWidth  = safetyPadding * (bounds.getWidth()
            + getPadding().getLeft() + getPadding().getRight()
            + getInsets().getLeft() + getInsets().getRight());
        double neededHeight = safetyPadding * (bounds.getHeight()
            + getPadding().getBottom() + getPadding().getTop()
            + getInsets().getBottom() + getInsets().getTop());

        setMinSize(neededWidth, neededHeight);
        setPrefSize(neededWidth, neededHeight);

        setOnMouseMoved(this::updateHighlghting);
        setOnMousePressed(this::handleClick);
        setOnMouseExited(event -> clearStyle(0, getLength()));
    }

    private void handleClick(MouseEvent mouseEvent) {
        CharacterHit hit = hit(mouseEvent.getX(), mouseEvent.getY());
        OptionalInt charIdx = hit.getCharacterIndex();
        if (charIdx.isPresent()) {
            AnnotatedString.TermElement elem = str.getTermElementAt(charIdx.getAsInt());
            SubtermSelector subtermSelector = elem.getSubtermSelector();
            listener.handleClickOnSubterm(term, subtermSelector);
        } else {
            // A click outside should select the whole item
            listener.handleClickOutsideTerm();
        }
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
