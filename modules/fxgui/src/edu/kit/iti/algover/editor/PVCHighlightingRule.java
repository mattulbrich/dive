package edu.kit.iti.algover.editor;

import edu.kit.iti.algover.parser.DafnyTree;
import edu.kit.iti.algover.proof.PVC;
import edu.kit.iti.algover.symbex.AssertionElement;
import edu.kit.iti.algover.symbex.PathConditionElement;
import edu.kit.iti.algover.symbex.SymbexPath;
import org.antlr.runtime.Token;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.List;
import java.util.stream.Collectors;

/**
 * Created by philipp on 30.06.17.
 */
public class PVCHighlightingRule implements HighlightingRule {

    private static class Span {
        final int beginLine, endLine, beginCharInLine, endCharInLine;

        private Span(int beginLine, int endLine, int beginCharInLine, int endCharInLine) {
            this.beginLine = beginLine;
            this.endLine = endLine;
            this.beginCharInLine = beginCharInLine;
            this.endCharInLine = endCharInLine;
        }

        private Span(Token token) {
            this(
                    token.getLine(),
                    token.getLine(),
                    token.getCharPositionInLine(),
                    token.getText() == null
                            ? -1
                            : token.getText().length() + token.getCharPositionInLine()
            );
        }

        private boolean isInvalid() {
            return beginCharInLine == -1;
        }
    }

    private static Span union(Span one, Span other) {
        if (one.isInvalid()) return other;
        if (other.isInvalid()) return one;
        return new Span(
                Math.min(one.beginLine, other.beginLine),
                Math.max(one.endLine, other.endLine),
                Math.min(one.beginCharInLine, other.beginCharInLine),
                Math.max(one.endCharInLine, other.endCharInLine)
        );
    }

    private static Span collectSpan(DafnyTree tree) {
        Span span = new Span(tree.getToken());
        return tree.getChildren().stream()
                .map(PVCHighlightingRule::collectSpan)
                .reduce(PVCHighlightingRule::union)
                .map(subSpan -> union(span, subSpan))
                .orElse(span);
    }

    private final List<Span> assignmentSpans;
    private final List<Span> positiveGuardSpans;
    private final List<Span> negativeGuardSpans;
    private final List<Span> allGuardSpans;
    private final List<Span> proofObligationSpans;

    public PVCHighlightingRule(PVC pvc) {
        SymbexPath symbexPath = pvc.getPathThroughProgram();

        List<DafnyTree> assignmentsAsList = new ArrayList<>();
        symbexPath.getAssignmentHistory().forEach(assignmentsAsList::add);
        assignmentSpans =
                assignmentsAsList.stream()
                        .map(PVCHighlightingRule::collectSpan)
                        .collect(Collectors.toList());

        List<PathConditionElement> pathConditionsAsList = new ArrayList<>();
        symbexPath.getPathConditions().forEach(pathConditionsAsList::add);

        positiveGuardSpans = pathConditionsAsList.stream()
                .filter(pathConditionElement -> pathConditionElement.getType() == PathConditionElement.AssumptionType.IF_THEN)
                .map(pathConditionElement -> collectSpan(pathConditionElement.getExpression()))
                .collect(Collectors.toList());

        negativeGuardSpans = pathConditionsAsList.stream()
                .filter(pathConditionElement -> pathConditionElement.getType() == PathConditionElement.AssumptionType.IF_ELSE)
                .map(pathConditionElement -> collectSpan(pathConditionElement.getExpression()))
                .collect(Collectors.toList());

        allGuardSpans = pathConditionsAsList.stream()
                .map(pathConditionElement -> collectSpan(pathConditionElement.getExpression()))
                .collect(Collectors.toList());

        List<AssertionElement> proofObligationsAsList = new ArrayList<>();
        symbexPath.getProofObligations().forEach(proofObligationsAsList::add);
        proofObligationSpans = proofObligationsAsList.stream()
                .map(assertionElement -> collectSpan(assertionElement.getOrigin()))
                .collect(Collectors.toList());

        // TODO: Find out what the tokens are for a method header. for example for the header
        // "method max(x: int, y: int) returns (m: int) {". That should still be highlighted
    }

    @Override
    public Collection<String> handleToken(Token token, Collection<String> syntaxClasses) {
        if (tokenInOneSpan(assignmentSpans, token)) {
            return syntaxClasses;
        } else if (tokenInOneSpan(proofObligationSpans, token)) {
            return syntaxClasses;
        } else if (tokenInOneSpan(allGuardSpans, token)) {
            if (tokenInOneSpan(positiveGuardSpans, token)) {
                return addClass(syntaxClasses, "guard-positive");
            } else if (tokenInOneSpan(negativeGuardSpans, token)) {
                return addClass(syntaxClasses, "guard-negative");
            } else {
                return syntaxClasses;
            }
        } else {
            return Collections.singletonList("lowlighted");
        }
    }

    private Collection<String> addClass(Collection<String> syntaxClasses, String cssClass) {
        List<String> classes = new ArrayList<>();
        classes.addAll(syntaxClasses);
        classes.add(cssClass);
        return classes;
    }

    private boolean tokenInOneSpan(List<Span> spans, Token token) {
        return spans.stream().anyMatch(span -> tokenInSpan(span, token));
    }

    private boolean tokenInSpan(Span span, Token token) {
        return between(token.getLine(), span.beginLine, span.endLine)
                && between(token.getCharPositionInLine(), span.beginCharInLine, span.endCharInLine);
    }

    private boolean between(int n, int low, int high) {
        return low <= n && n <= high;
    }

}
