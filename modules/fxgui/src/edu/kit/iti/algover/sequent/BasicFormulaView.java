/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.sequent;

import edu.kit.iti.algover.rules.SubtermSelector;
import edu.kit.iti.algover.rules.TermSelector;
import edu.kit.iti.algover.sequent.formulas.ViewFormula;
import edu.kit.iti.algover.term.prettyprint.AnnotatedString;
import edu.kit.iti.algover.term.prettyprint.PrettyPrint;
import edu.kit.iti.algover.util.*;
import javafx.beans.property.SimpleObjectProperty;
import javafx.collections.ListChangeListener;
import javafx.collections.ObservableList;
import javafx.geometry.Bounds;
import javafx.scene.input.KeyCode;
import javafx.scene.input.MouseEvent;
import org.fxmisc.richtext.CharacterHit;
import org.fxmisc.richtext.CodeArea;

import java.util.ArrayList;
import java.util.List;
import java.util.OptionalInt;
import java.util.stream.Collectors;

/**
 * Created by Philipp on 22.07.2017.
 * updated by JonasKlamroth on 28.5.19
 *
 * This Class implements the basic styling of a Cell of the ListViews for the sequent in the {@link SequentController}.
 */
public class BasicFormulaView extends CodeArea {

    /**
     * Different presets for Priorities of Styles. Styles with lower priority get overwritten by styles
     * with higher prio.
     */
    public class StylePrios {
        public static final int MOUSEOVER = 30;
        public static final int FORMULATYPE = 10;
        public static final int SELECTED = 20;
    }

    /**
     * The model for this view. The formula which is displayed.
     */
    protected final ViewFormula formula;
    /**
     * A annotated String containing the formula for this view with annotated TermSelector information.
     */
    protected AnnotatedString annotatedString;
    /**
     * The element which is currently highlighted by the mouse (mouseover).
     */
    private AnnotatedString.TermElement highlightedElement;
    /**
     * the last term that was clicked on.
     */
    private final SimpleObjectProperty<TermSelector> selectedTerm;
    /**
     * the last term that was ctr-clicked on.
     */
    private final SimpleObjectProperty<TermSelector> selectedReference;
    /**
     * List of all styles of the SequentController
     */
    ObservableList<Quadruple<TermSelector, String, Integer, String>> allStyles;
    /**
     * Locally applied Styles.
     */
    private List<Quadruple<TermSelector, String, Integer, String>> localStyles;
    /**
     * The Styles from {@link #allStyles} which affect this view.
     */
    private List<Quadruple<TermSelector, String, Integer, String>> relevantGlobalStyles;

    public BasicFormulaView(ViewFormula formula, SimpleObjectProperty<TermSelector> selectedTerm,
                            SimpleObjectProperty<TermSelector> selectedReference,
                            ObservableList<Quadruple<TermSelector, String, Integer, String>> allStyles) {
        super("");

        this.formula = formula;
        this.localStyles = new ArrayList<>();
        this.selectedTerm = selectedTerm;
        this.selectedReference = selectedReference;
        this.allStyles = allStyles;
        allStyles.addListener(new ListChangeListener<Quadruple<TermSelector, String, Integer, String>>() {
            @Override
            public void onChanged(Change<? extends Quadruple<TermSelector, String, Integer, String>> c) {
                relevantGlobalStyles = allStyles.stream().filter(x ->
                        x.fst.getPolarity() == formula.getPolarity() &&
                                x.fst.getTermNo() == formula.getIndexInSequent()).collect(Collectors.toList());
                updateStyleClasses();
            }
        });

        relevantGlobalStyles = allStyles.stream().filter(x ->
                x.fst.getPolarity() == formula.getPolarity() &&
                        x.fst.getTermNo() == formula.getIndexInSequent()).collect(Collectors.toList());
        getStyleClass().add("formula-view");
        setFocusTraversable(false);
        setEditable(false);

        //This might be a problem with increasing size of Proofs
        selectedTerm.addListener(this::updateSelected);
        selectedReference.addListener(this::updateSelectedRef);

        applyBaseStyle();

        relayout();

        setOnMouseClicked(event -> {
            if(highlightedElement != null) {
                if(event.isControlDown()) {
                    selectedReference.set(getMouseOverSelector());
                } else {selectedTerm.set(getMouseOverSelector());}
            }
        });
        setOnMouseMoved(this::handleHover);
        setOnMouseExited(event -> {
            removeStyle("highlight");
            updateStyleClasses();
        });

        widthProperty().addListener(x -> relayout());
    }

    @Override
    protected void finalize() throws Throwable {
        super.finalize();
        selectedTerm.removeListener(this::updateSelected);
        selectedReference.removeListener(this::updateSelectedRef);
    }

    private TermSelector getMouseOverSelector() {
        return new TermSelector(formula.getTermSelector(), highlightedElement.getSubtermSelector());
    }

    private void updateSelected(javafx.beans.value.ObservableValue<? extends TermSelector> observableValue, TermSelector oldV, TermSelector newV) {
        removeStyle("selected");
        if(newV != null && newV.getPolarity() == formula.getPolarity() && newV.getTermNo() == formula.getIndexInSequent()) {
            addStyleForTerm(newV, "selected", StylePrios.SELECTED, "selected");
        }
        updateStyleClasses();
    }

    private void updateSelectedRef(javafx.beans.value.ObservableValue<? extends TermSelector> observableValue, TermSelector oldV, TermSelector newV) {
        removeStyle("selectedRef");
        if(newV != null && newV.getPolarity() == formula.getPolarity() && newV.getTermNo() == formula.getIndexInSequent()) {
            addStyleForTerm(newV, "selectedRef", StylePrios.SELECTED + 1, "selectedRef");
        }
        updateStyleClasses();
    }

    private String styleForType() {
        switch (formula.getType()) {
            case ADDED:
                return "formula-added";
            case DELETED:
                return "formula-deleted";
            default:
                return null;
        }
    }

    private void applyBaseStyle() {
        String typeStyle = styleForType();
        if(typeStyle != null) {
            addStyleForTerm(formula.getTermSelector(), typeStyle, StylePrios.FORMULATYPE, "formula-type");
        }
        for(TermSelector ts : formula.getChangedTerms()) {
            addStyleForTerm(ts, "formula-modified", StylePrios.FORMULATYPE, "modified-parts");
        }
        updateStyleClasses();
    }

    protected void handleHover(MouseEvent mouseEvent) {
        CharacterHit hit = hit(mouseEvent.getX(), mouseEvent.getY());
        OptionalInt charIdx = hit.getCharacterIndex();
        if (charIdx.isPresent()) {
            removeStyle("highlight");
            highlightedElement = annotatedString.getTermElementAt(charIdx.getAsInt());
            addStyleForTerm(new TermSelector(formula.getPolarity(), formula.getIndexInSequent(), highlightedElement.getSubtermSelector()), "highlighted", StylePrios.MOUSEOVER, "highlight");
        } else {
            highlightedElement = null;
        }
        updateStyleClasses();
    }

    /**
     * Applies all currently set Styleclasses
     */
    protected void updateStyleClasses() {
        List<Quadruple<TermSelector, String, Integer, String>>  relavantStyles = relevantGlobalStyles;
        relavantStyles.addAll(localStyles);
        clearStyle(0, getLength());
        relavantStyles.sort((o1, o2) -> o1.trd > o2.trd ? 1 : o1.trd == o2.trd ? 0 : -1);
        for(Quadruple<TermSelector, String, Integer, String> t : relavantStyles) {
            setStyleForTerm(t.fst, t.snd);
        }
    }

    /**
     * Adds a style class for a certain Term.
     * @param ts A termselector pointing to the term to be styled.
     * @param styleClass The style class to be applied (has to be found int style.css
     * @param prio A priority of the Style (determines which style will be applied when localStyles clash)
     * @param id An id to remove the style later on.
     */
    public void addStyleForTerm(TermSelector ts, String styleClass, int prio, String id) {
        allStyles.add(new Quadruple<>(ts, styleClass, prio, id));
    }

    /**
     * Removes a style from the currently applied localStyles
     * @param id The id associated with the style to be removed (see {@link #addStyleForTerm(TermSelector, String, int, String)})
     */
    public void removeStyle(String id) {
        allStyles.removeIf(x -> x.fth.equals(id));
    }

    /**
     * Applies a styleClass to a given Term (localStyles added like this will be overwritten with the next style to avoid this use add style instead)
     * @param ts A Termselector pointing to the term to be styled
     * @param styleClass the styleclass to be applied
     */
    public void setStyleForTerm(TermSelector ts, String styleClass) {
        if(annotatedString != null) {
            if(ts.getSubtermSelector().getDepth() == 0) {
                setStyleClass(0, getText().length(), styleClass);
                return;
            }
            List<AnnotatedString.TermElement> elements = annotatedString.getAllTermElements();
            elements = elements.stream().filter(
                    x -> x.getSubtermSelector().equals(ts.getSubtermSelector())
                            && ts.getPolarity() == formula.getPolarity())
                    .collect(Collectors.toList());
            if (elements.size() == 0) {
                return;
                //throw new IllegalArgumentException("Termselector not present in this view.");
            } else if (elements.size() > 1) {
                return;
                //throw new RuntimeException("this should not happen: Several Annotated Strings with same ts.");
            }
            AnnotatedString.TermElement element = elements.get(0);
            setStyleClass(element.getBegin(), element.getEnd(), styleClass);
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
