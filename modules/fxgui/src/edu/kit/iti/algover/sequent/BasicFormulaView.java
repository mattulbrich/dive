/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.sequent;

import com.sun.javafx.css.PseudoClassState;
import edu.kit.iti.algover.rules.SubtermSelector;
import edu.kit.iti.algover.rules.TermSelector;
import edu.kit.iti.algover.sequent.formulas.TopLevelFormula;
import edu.kit.iti.algover.term.prettyprint.AnnotatedString;
import edu.kit.iti.algover.term.prettyprint.PrettyPrint;
import edu.kit.iti.algover.util.SubSelection;
import edu.kit.iti.algover.util.TextUtil;
import javafx.geometry.Bounds;
import javafx.scene.input.MouseEvent;
import org.fxmisc.richtext.CharacterHit;
import org.fxmisc.richtext.CodeArea;

import java.util.HashSet;
import java.util.OptionalInt;
import java.util.Set;
import java.util.stream.Collectors;

/**
 * Created by Philipp on 22.07.2017.
 * Updated by S.Grebing
 */
public class BasicFormulaView extends CodeArea {

    protected final TopLevelFormula formula;
    protected final SubSelection<AnnotatedString.TermElement> mouseOverTerm;

    protected AnnotatedString annotatedString;
    protected AnnotatedString.TermElement highlightedElement;
    protected Set<AnnotatedString.TermElement> historyHighlights;

    private Set<TermSelector> selectorsToHighlight;

    public BasicFormulaView(TopLevelFormula formula,
                            SubSelection<AnnotatedString.TermElement> mouseOverTerm,
                            Set<TermSelector> selectorsToHighlight) {
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

        this.selectorsToHighlight = selectorsToHighlight;

        widthProperty().addListener(x -> relayout());
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

    private void highlightHistorySelections(Set<AnnotatedString.TermElement> historyHighlights, String cssClass) {
        if(historyHighlights != null) {
            for (AnnotatedString.TermElement highlight : historyHighlights) {
                if (highlight != null) {
                    setStyleClass(highlight.getBegin(), highlight.getEnd(), cssClass);


                }
            }
        }
    }

    protected void highlightFromElement(AnnotatedString.TermElement termElement, String cssClass) {
        if (termElement != null) {
            setStyleClass(termElement.getBegin(), termElement.getEnd(), cssClass);
        }
    }

    @Override
    protected double computePrefHeight(double width) {
        String prettyPrinted = calculateText(width);
        double neededHeight = calculateNeededHeight(prettyPrinted);
        return neededHeight;
    }

    protected void relayout() {
        double width = getWidth();

        String prettyPrinted = calculateText(width);
        double neededHeight = calculateNeededHeight(prettyPrinted);

        replaceText(0, getLength(), prettyPrinted);
        updateStyleClasses();

        if(this.selectorsToHighlight != null) {
            this.historyHighlights = this.selectorsToHighlight.stream().map(termSelector -> {
                return getTermElementBySubtermSelector(termSelector.getSubtermSelector(), this.annotatedString);
            }).collect(Collectors.toSet());
        } else {
            this.historyHighlights = new HashSet<>();
        }

        highlightHistorySelections(this.historyHighlights, "historyHighlight");

        if(width != 0.0) {
            // Set this only if a width has been set.
            setMinHeight(neededHeight);
            setPrefHeight(neededHeight);
            setHeight(neededHeight);
        }
    }

    // Calculates text and updates annotatedString
    private String calculateText(double width) {
        // Find out how many characters the text can be wide:
        Bounds mChar = TextUtil.computeTextBounds("m", getStyleClass(), getStylesheets());

        double charWidth = mChar.getWidth();

        int charsFitting = (int) (width / charWidth);

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

    /**
     * Compute the AnnotatedString.TermElement from a given SubtermSelector and AnnotatedString
     * @param selector
     * @param string
     * @return
     */
    protected AnnotatedString.TermElement getTermElementBySubtermSelector(SubtermSelector selector, AnnotatedString string) {
        if (selector == null || string == null) {
            return null;
        }
        if (selector.getDepth() == 0) {
            return string.getEnvelopingTermElement();
        }
        AnnotatedString.TermElement termElement1 = string.getAllTermElements().stream()
                .filter(termElement -> termElement.getSubtermSelector().equals(selector))
                .findFirst().orElse(null);
        return termElement1;
    }


}
