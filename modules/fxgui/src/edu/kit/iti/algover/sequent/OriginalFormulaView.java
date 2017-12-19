package edu.kit.iti.algover.sequent;

import edu.kit.iti.algover.rules.SubtermSelector;
import edu.kit.iti.algover.sequent.formulas.OriginalFormula;
import edu.kit.iti.algover.term.prettyprint.AnnotatedString;
import edu.kit.iti.algover.util.SubSelection;
import javafx.beans.value.ObservableValue;
import javafx.event.Event;
import javafx.scene.input.MouseEvent;
import org.fxmisc.richtext.CharacterHit;

import java.util.OptionalInt;

public class OriginalFormulaView extends BasicFormulaView {

    private final OriginalFormula originalFormula;

    protected final SubSelection<SubtermSelector> referenceSelection;
    protected final SubSelection<SubtermSelector> lastClickedTerm;

    public OriginalFormulaView(OriginalFormula formula, SubSelection<SubtermSelector> referenceSelection, SubSelection<SubtermSelector> lastClickedTerm, SubSelection<AnnotatedString.TermElement> mouseOverTerm) {
        super(formula, mouseOverTerm);
        this.originalFormula = formula;
        this.referenceSelection = referenceSelection;
        this.lastClickedTerm = lastClickedTerm;

        setOnMousePressed(this::handleClick);
        referenceSelection.selected().addListener(this::updateReferenceSelected);
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
}
