/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.sequent;

import edu.kit.iti.algover.rules.SubtermSelector;
import edu.kit.iti.algover.sequent.formulas.TopLevelFormula;
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
public class BasicFormulaView extends CodeArea {

    protected final TopLevelFormula formula;
    protected final SubSelection<AnnotatedString.TermElement> mouseOverTerm;

    protected AnnotatedString annotatedString;
    protected AnnotatedString.TermElement highlightedElement;

    public BasicFormulaView(TopLevelFormula formula, SubSelection<AnnotatedString.TermElement> mouseOverTerm) {
        super("");

        this.formula = formula;
        this.mouseOverTerm = mouseOverTerm;

        getStyleClass().add("formula-view");
        setFocusTraversable(false);
        setEditable(false);

        relayout();

        setOnMouseMoved(this::handleHover);
        setOnMouseExited(event -> {
            highlightedElement = null;
            updateStyleClasses();
        });
    }

    protected void handleHover(MouseEvent mouseEvent) {
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

    protected void updateStyleClasses() {
        clearStyle(0, getLength());
        highlightFromElement(highlightedElement, "highlighted");
    }

    protected void highlightFromElement(AnnotatedString.TermElement termElement, String cssClass) {
        if (termElement != null) {
            setStyleClass(termElement.getBegin(), termElement.getEnd(), cssClass);
        }
    }

    protected void layoutChildren() {
        super.layoutChildren();
        relayout();
    }

    protected void relayout() {
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
        this.annotatedString = p.print(formula.getTerm(), Math.max(20, charsFitting));

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

    protected AnnotatedString.TermElement getTermElementBySubtermSelector(SubtermSelector selector, AnnotatedString string) {
        if (selector == null) {
            return null;
        }
        if (selector.getDepth() == 0) {
            return string.getEnvelopingTermElement();
        }
        return string.getAllTermElements().stream()
                .filter(termElement -> termElement.getSubtermSelector().equals(selector))
                .findFirst().orElse(null);
    }

}
