/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.sequent;

import edu.kit.iti.algover.term.prettyprint.AnnotatedString;
import edu.kit.iti.algover.term.prettyprint.PrettyPrint;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.term.prettyprint.SubtermSelector;
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
    private final TermViewListener listener;
    private AnnotatedString annotatedString;
    private AnnotatedString.TermElement highlightedElement;

    public TermView(Term term, TermViewListener listener) {
        super("");

        this.term = term;
        this.listener = listener;

        getStyleClass().add("term-view");
        setFocusTraversable(false);
        setEditable(false);

        relayout();

        setOnMouseMoved(this::updateHighlighting);
        setOnMousePressed(this::handleClick);
        setOnMouseExited(event -> {
            highlightedElement = null;
            clearStyle(0, getLength());
        });
    }

    private void relayout() {
        String prettyPrinted = calculateText();
        double neededHeight = calculateNeededHeight(prettyPrinted);

        replaceText(0, getLength(), prettyPrinted);
        if (highlightedElement != null) {
            setStyleClass(highlightedElement.getBegin(), highlightedElement.getEnd(), "highlighted");
        }
        setMinHeight(neededHeight);
        setPrefHeight(neededHeight);
        setHeight(neededHeight);
    }

    // Calculates text and updates annotatedString
    private String calculateText() {
        // Find out how many characters the text can be wide:
        Bounds mChar = TextUtil.computeTextBounds("m", getStyleClass(), getStylesheets());

        double charWidth = mChar.getWidth();

        int charsFitting = (int) (getWidth() / charWidth);

        // Prettyprint the term with the given amount of char width
        PrettyPrint p = new PrettyPrint();
        this.annotatedString = p.print(term, Math.max(20, charsFitting));

        return annotatedString.toString();
    }

    private double calculateNeededHeight(String text) {
        // This is a hack, but it seems to be impossible without it...
        Bounds bounds = TextUtil.computeTextBounds(text, getStyleClass(), getStylesheets());

        final double safetyPadding = 1.1; // 10%, this is such a hack ... :(

        return safetyPadding * (bounds.getHeight()
            + getPadding().getBottom() + getPadding().getTop()
            + getInsets().getBottom() + getInsets().getTop());
    }

    private void handleClick(MouseEvent mouseEvent) {
        CharacterHit hit = hit(mouseEvent.getX(), mouseEvent.getY());
        OptionalInt charIdx = hit.getCharacterIndex();
        if (charIdx.isPresent()) {
            AnnotatedString.TermElement elem = annotatedString.getTermElementAt(charIdx.getAsInt());
            SubtermSelector subtermSelector = elem.getSubtermSelector();
            listener.handleClickOnSubterm(term, subtermSelector);
        } else {
            // A click outside should select the whole item
            listener.handleClickOutsideTerm();
        }
    }

    private void updateHighlighting(MouseEvent mouseEvent) {
        CharacterHit hit = hit(mouseEvent.getX(), mouseEvent.getY());
        OptionalInt charIdx = hit.getCharacterIndex();
        if (charIdx.isPresent()) {
            highlightedElement = annotatedString.getTermElementAt(charIdx.getAsInt());
            clearStyle(0, getLength());
            setStyleClass(highlightedElement.getBegin(), highlightedElement.getEnd(), "highlighted");
        } else {
            clearStyle(0, getLength());
        }
    }

    protected void layoutChildren() {
        super.layoutChildren();
        relayout();
    }

}
