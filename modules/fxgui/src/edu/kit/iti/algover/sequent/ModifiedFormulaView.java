package edu.kit.iti.algover.sequent;

import edu.kit.iti.algover.sequent.formulas.ModifiedFormula;
import edu.kit.iti.algover.term.prettyprint.AnnotatedString;
import edu.kit.iti.algover.util.SubSelection;

import java.util.List;
import java.util.stream.Stream;

public class ModifiedFormulaView extends BasicFormulaView {

    private final ModifiedFormula modifiedFormula;

    public ModifiedFormulaView(ModifiedFormula formula, SubSelection<AnnotatedString.TermElement> mouseOverTerm) {
        super(formula, mouseOverTerm);
        this.modifiedFormula = formula;
    }

    @Override
    protected void updateStyleClasses() {
        // TODO this is weird. I would expect to recalculate the highlighted term in the "relayout" method...
        // but the annotatedString changes in between
        calculateHighlighted().forEach(termElement -> highlightFromElement(termElement, "modified"));
    }

    private Stream<AnnotatedString.TermElement> calculateHighlighted() {
        // This is not really pretty too. This is because updateStyleClasses is called by the super-constructor
        // before this constructor ran through...
        if (modifiedFormula == null) {
            return null;
        }

        return modifiedFormula.getModifiedParts().stream().map(modifiedSelector -> {
            if (modifiedSelector.getPath().size() == 0) {
                return annotatedString.getEnvelopingTermElement();
            } else {
                return annotatedString.getAllTermElements().stream()
                        .filter(termElement -> termElement.getSubtermSelector().equals(modifiedSelector))
                        .findFirst()
                        .orElseThrow(() -> new RuntimeException("Cannot find TermElement for modified term part."));
            }
        });
    }

}
