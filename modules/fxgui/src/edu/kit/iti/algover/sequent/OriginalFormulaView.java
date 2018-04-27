package edu.kit.iti.algover.sequent;

import edu.kit.iti.algover.rules.SubtermSelector;
import edu.kit.iti.algover.rules.TermSelector;
import edu.kit.iti.algover.sequent.formulas.OriginalFormula;
import edu.kit.iti.algover.term.prettyprint.AnnotatedString;
import edu.kit.iti.algover.util.SubSelection;
import javafx.beans.value.ObservableValue;
import javafx.event.Event;
import javafx.scene.input.MouseEvent;
import org.fxmisc.richtext.CharacterHit;

import java.util.List;
import java.util.OptionalInt;

public class OriginalFormulaView extends BasicFormulaView {

    private final OriginalFormula originalFormula;
    protected final TermSelector.SequentPolarity polarity;

    protected final SubSelection<SubtermSelector> referenceSelection;
    protected final SubSelection<SubtermSelector> lastClickedTerm;

    public OriginalFormulaView(
            OriginalFormula formula,
            TermSelector.SequentPolarity polarity,
            SubSelection<TermSelector> referenceSelection,
            SubSelection<TermSelector> lastClickedTerm,
            SubSelection<AnnotatedString.TermElement> mouseOverTerm) {
        super(formula, mouseOverTerm);
        this.originalFormula = formula;
        this.polarity = polarity;
        this.referenceSelection = referenceSelection.subSelection(this::reduceTermSelector, this::liftSubtermSelector);
        this.lastClickedTerm = lastClickedTerm.subSelection(this::reduceTermSelector, this::liftSubtermSelector);

        setOnMousePressed(this::handleClick);
        this.referenceSelection.selected().addListener(this::updateReferenceSelected);
    }

    private void updateReferenceSelected(ObservableValue<? extends SubtermSelector> obs, SubtermSelector before, SubtermSelector selected) {
        updateStyleClasses();
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

    @Override
    protected void updateStyleClasses() {
        super.updateStyleClasses();
        if (referenceSelection != null) {
            highlightFromElement(calculateReferenceSelected(), "reference-selected");
        }
    }

    private AnnotatedString.TermElement calculateReferenceSelected() {
        return getTermElementBySubtermSelector(referenceSelection.selected().get(), annotatedString);
    }

    /**
     * @param termSelector the term selector that may update this view's selected subterm.
     * @return either null, if the term selector points at another top-level term, or
     *         the extracted subterm selector if it pointed to this formula.
     */
    private SubtermSelector reduceTermSelector(TermSelector termSelector) {
        if (termSelector != null && termSelector.getPolarity() == polarity && termSelector.getTermNo() == originalFormula.getIndexInSequent()) {
            return termSelector.getSubtermSelector();
        } else {
            return null;
        }
    }

    /**
     * @param subtermSelector the selector that points to a subterm within this formula.
     * @return the given subterm lifted to a term selector that points at the correct forumla index and polarity in the
     *         sequent.
     */
    private TermSelector liftSubtermSelector(SubtermSelector subtermSelector) {
        List<Integer> pathAsList = subtermSelector.getPath();
        int[] path = new int[pathAsList.size()];
        for (int i = 0; i < path.length; i++) {
            path[i] = pathAsList.get(i);
        }
        return new TermSelector(polarity, originalFormula.getIndexInSequent(), path);
    }
}
