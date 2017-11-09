/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.sequent;

import edu.kit.iti.algover.rules.SubtermSelector;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.term.prettyprint.AnnotatedString;
import edu.kit.iti.algover.term.prettyprint.PrettyPrint;
import edu.kit.iti.algover.util.SubSelection;
import edu.kit.iti.algover.util.TextUtil;
import javafx.beans.value.ObservableValue;
import javafx.event.Event;
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
    private final SubSelection<SubtermSelector> referenceSelection;
    private final SubSelection<SubtermSelector> lastClickedTerm;
    private final SubSelection<AnnotatedString.TermElement> mouseOverTerm;

    private AnnotatedString annotatedString;
    private AnnotatedString.TermElement highlightedElement;
    private AnnotatedString.TermElement referenceSelectedElement;


    public TermView(Term term,
                    SubSelection<SubtermSelector> referenceSelection,
                    SubSelection<SubtermSelector> lastClickedTerm,
                    SubSelection<AnnotatedString.TermElement> mouseOverTerm) {
        super("");

        this.term = term;
        this.referenceSelection = referenceSelection;
        this.lastClickedTerm = lastClickedTerm;
        this.mouseOverTerm = mouseOverTerm;

        getStyleClass().add("term-view");
        setFocusTraversable(false);
        setEditable(false);

        relayout();

        setOnMouseMoved(this::handleHover);
        setOnMousePressed(this::handleClick);
        setOnMouseExited(event -> {
            highlightedElement = null;
            updateStyleClasses();
        });
        referenceSelection.selected().addListener(this::updateSelectedSubterm);
    }

    private void updateSelectedSubterm(ObservableValue<? extends SubtermSelector> obs, SubtermSelector before, SubtermSelector selected) {
        AnnotatedString.TermElement selectedBefore = referenceSelectedElement;
        if (selected != null) {
            referenceSelectedElement = annotatedString.getAllTermElements().stream()
                    .filter(termElement -> termElement.getSubtermSelector().equals(selected))
                    .findFirst().orElse(null);
            if (referenceSelectedElement == null) {
                referenceSelectedElement = annotatedString.getEnvelopingTermElement();
            }
        } else {
            referenceSelectedElement = null;
        }
        if (selectedBefore != referenceSelectedElement) {
            updateStyleClasses();
        }
    }

    private void relayout() {
        String prettyPrinted = calculateText();
        double neededHeight = calculateNeededHeight(prettyPrinted);

        replaceText(0, getLength(), prettyPrinted);
        updateStyleClasses();

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
            SubtermSelector selector = elem.getSubtermSelector();

            if (mouseEvent.isControlDown()) {
                referenceSelection.select(selector);
            } else {
                lastClickedTerm.select(selector);
            }
        } else {
            Event.fireEvent(this.getParent(), mouseEvent);
        }
    }

    private void handleHover(MouseEvent mouseEvent) {
        CharacterHit hit = hit(mouseEvent.getX(), mouseEvent.getY());
        OptionalInt charIdx = hit.getCharacterIndex();
        if (charIdx.isPresent()) {
            highlightedElement = annotatedString.getTermElementAt(charIdx.getAsInt());
        } else {
            highlightedElement = null;
        }
        mouseOverTerm.select(highlightedElement);
        updateStyleClasses();
    }

    private void updateStyleClasses() {
        clearStyle(0, getLength());
        highlightFromElement(highlightedElement, "highlighted");
        highlightFromElement(referenceSelectedElement, "reference-selected");
    }

    private void highlightFromElement(AnnotatedString.TermElement termElement, String cssClass) {
        if (termElement != null) {
            setStyleClass(termElement.getBegin(), termElement.getEnd(), cssClass);
        }
    }

    protected void layoutChildren() {
        super.layoutChildren();
        relayout();
    }

}
