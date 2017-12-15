package edu.kit.iti.algover.sequent;

import edu.kit.iti.algover.sequent.formulas.ModifiedFormula;
import edu.kit.iti.algover.term.prettyprint.AnnotatedString;
import edu.kit.iti.algover.util.SubSelection;

public class ModifiedFormulaView extends BasicFormulaView {

    private final ModifiedFormula modifiedFormula;

    private AnnotatedString.TermElement modifiedTermElement;

    public ModifiedFormulaView(ModifiedFormula formula, SubSelection<AnnotatedString.TermElement> mouseOverTerm) {
        super(formula, mouseOverTerm);
        this.modifiedFormula = formula;
    }

    @Override
    protected void updateStyleClasses() {
        // TODO this is weird. I would expect to recalculate the highlighted term in the "relayout" method...
        // but the annotatedString changes in between
        calculateHighlighted();
        highlightFromElement(modifiedTermElement, "modified");
    }

    private void calculateHighlighted() {
        // This is not really pretty too. This is because updateStyleClasses is called by the super-constructor
        // before this constructor ran through...
        if (modifiedFormula == null) {
            return;
        }
        if (modifiedFormula.getModifiedPart().getPath().size() == 0) {
            modifiedTermElement = annotatedString.getEnvelopingTermElement();
        } else {
            modifiedTermElement =
                    annotatedString.getAllTermElements().stream()
                            .filter(termElement -> termElement.getSubtermSelector().equals(modifiedFormula.getModifiedPart()))
                            .findFirst()
                            .orElseThrow(() -> new RuntimeException("Cannot find TermElement for modified term part."));
        }
    }

}
