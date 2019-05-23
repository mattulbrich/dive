/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.sequent;

import edu.kit.iti.algover.rules.SubtermSelector;
import edu.kit.iti.algover.rules.TermSelector;
import edu.kit.iti.algover.sequent.formulas.ModifiedFormula;
import edu.kit.iti.algover.sequent.formulas.OriginalFormula;
import edu.kit.iti.algover.term.prettyprint.AnnotatedString;
import edu.kit.iti.algover.util.SubSelection;

import java.util.List;
import java.util.stream.Stream;

public class ModifiedFormulaView extends OriginalFormulaView {

    private final ModifiedFormula modifiedFormula;

    public ModifiedFormulaView(
            ModifiedFormula formula,
            TermSelector.SequentPolarity polarity,
            SubSelection<TermSelector> referenceSelection,
            SubSelection<TermSelector> lastClickedTerm,
            SubSelection<AnnotatedString.TermElement> mouseOverTerm) {
        super(formula, polarity, referenceSelection, lastClickedTerm, mouseOverTerm);
        this.modifiedFormula = formula;
    }

    @Override
    protected void updateStyleClasses() {
        // TODO this is weird. I would expect to recalculate the highlighted term in the "relayout" method...
        // but the annotatedString changes in between
        // FIXME NullPointer!
        calculateHighlighted().forEach(termElement -> highlightFromElement(termElement, "modified"));
        highlightFromElement(highlightedElement, "highlighted");
    }

    private Stream<AnnotatedString.TermElement> calculateHighlighted() {
        // This is not really pretty too. This is because updateStyleClasses is called by the super-constructor
        // before this constructor ran through...
        if (modifiedFormula == null) {
            return Stream.empty();
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

    /**
     * @param subtermSelector the selector that points to a subterm within this formula.
     * @return the given subterm lifted to a term selector that points at the correct forumla index and polarity in the
     * sequent.
     */
    private TermSelector liftSubtermSelector(SubtermSelector subtermSelector) {
        List<Integer> pathAsList = subtermSelector.getPath();
        int[] path = new int[pathAsList.size()];
        for (int i = 0; i < path.length; i++) {
            path[i] = pathAsList.get(i);
        }
        return new TermSelector(polarity, modifiedFormula.getIndexInSequent(), path);
    }

}
