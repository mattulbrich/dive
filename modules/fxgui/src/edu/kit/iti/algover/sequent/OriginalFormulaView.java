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

    protected AnnotatedString.TermElement referenceSelectedElement;
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
        highlightFromElement(referenceSelectedElement, "reference-selected");
    }
}
