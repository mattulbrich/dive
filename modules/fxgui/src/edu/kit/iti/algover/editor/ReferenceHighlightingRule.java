package edu.kit.iti.algover.editor;

import edu.kit.iti.algover.references.CodeReference;
import edu.kit.iti.algover.util.Span;
import org.antlr.runtime.Token;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

public class ReferenceHighlightingRule extends SpanHighlightingRule {

    private final List<Span> backlightedSpans;

    public ReferenceHighlightingRule(Set<CodeReference> codeReferences) {
        this.backlightedSpans = codeReferences.stream()
                .map(this::referenceToSpan)
                .collect(Collectors.toList());
        System.out.println(backlightedSpans);
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
