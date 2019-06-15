/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.editor;

import edu.kit.iti.algover.references.CodeReference;
import edu.kit.iti.algover.util.Span;
import org.antlr.runtime.Token;

import java.util.Collection;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

/**
 * This highlighting rule implements highlighting a set of references into the
 * code.
 * <p>
 * This is for example used for highlighting the parts of the code that resulted
 * in a term that the user selected to find the origin of.
 */
public class ReferenceHighlightingRule extends SpanHighlightingRule {

    private final List<Span> backlightedSpans;

    /**
     * @param codeReferences a set of {@link CodeReference}s to highlight in the {@link DafnyCodeArea}.
     *                       Highlighted spans get the "reference-backlighted" class added.
     */
    public ReferenceHighlightingRule(Set<CodeReference> codeReferences) {
        this.backlightedSpans = codeReferences.stream()
                .map(this::referenceToSpan)
                .collect(Collectors.toList());
    }

    private Span referenceToSpan(CodeReference codeReference) {
        return spanFromStartEnd(codeReference.getStartToken(), codeReference.getEndToken());
    }

    @Override
    public Collection<String> handleToken(Token token, Collection<String> syntaxClasses) {
        if (tokenInOneSpan(backlightedSpans, token)) {
            return addClass(syntaxClasses, "reference-backlighted");
        } else {
            return syntaxClasses;
        }
    }
}
