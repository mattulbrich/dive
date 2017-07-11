package edu.kit.iti.algover.editor;

import edu.kit.iti.algover.parser.DafnyParser;
import edu.kit.iti.algover.parser.DafnyTree;
import edu.kit.iti.algover.proof.PVC;
import edu.kit.iti.algover.symbex.AssertionElement;
import edu.kit.iti.algover.symbex.PathConditionElement;
import edu.kit.iti.algover.symbex.SymbexPath;
import org.antlr.runtime.Token;

import java.util.*;
import java.util.function.Predicate;
import java.util.stream.Collectors;

/**
 * Created by philipp on 30.06.17.
 */
public class PVCHighlightingRule implements HighlightingRule {

    // Helper class for defining "selections" of to-be-highlighted code
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
                            ? token.getCharPositionInLine()
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

    private static Token minPos(Token token1, Token token2) {
        if (token1.getLine() < token2.getLine()) {
            return token1;
        } else if (token2.getLine() < token1.getLine()) {
            return token2;
        }
        if (token1.getCharPositionInLine() < token2.getCharPositionInLine()) {
            return token1;
        } else {
            return token2;
        }
    }

    // Creates a Span from a DafnyTree
    private static Span collectSpan(DafnyTree tree) {
        return union(
                new Span(tree.getStartToken()),
                new Span(tree.getStopToken()));
    }

    private final List<Span> assignmentSpans;
    private final List<Span> positiveGuardSpans;
    private final List<Span> negativeGuardSpans;
    private final List<Span> allGuardSpans;
    private final List<Span> proofObligationSpans;
    private final Span methodHeaderSpan;

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
                .filter(this::isPositiveGuard)
                .map(PathConditionElement::getExpression)
                .map(PVCHighlightingRule::collectSpan)
                .collect(Collectors.toList());

        negativeGuardSpans = pathConditionsAsList.stream()
                .filter(this::isNegativeGuard)
                .map(PathConditionElement::getExpression)
                .map(PVCHighlightingRule::collectSpan)
                .collect(Collectors.toList());

        allGuardSpans = pathConditionsAsList.stream()
                .map(PathConditionElement::getExpression)
                .map(PVCHighlightingRule::collectSpan)
                .collect(Collectors.toList());

        List<AssertionElement> proofObligationsAsList = new ArrayList<>();
        symbexPath.getProofObligations().forEach(proofObligationsAsList::add);
        proofObligationSpans = proofObligationsAsList.stream()
                .map(AssertionElement::getOrigin)
                .map(PVCHighlightingRule::collectSpan)
                .collect(Collectors.toList());

        List<DafnyTree> treesAfterMethodHeader = new ArrayList<>();
        treesAfterMethodHeader.add(symbexPath.getMethod().getFirstChildWithType(DafnyParser.REQUIRES));
        treesAfterMethodHeader.add(symbexPath.getMethod().getFirstChildWithType(DafnyParser.ENSURES));
        treesAfterMethodHeader.add(symbexPath.getMethod().getFirstChildWithType(DafnyParser.DECREASES));

        Token firstTokenAfterHeader = treesAfterMethodHeader.stream()
                .filter(Objects::nonNull)
                .map(DafnyTree::getStartToken)
                .reduce(PVCHighlightingRule::minPos)
                .orElseThrow(() -> new IllegalStateException(
                        "It shouldn't be possible to not have any requires/ensures/decreases after method."));

        Token methodStart = symbexPath.getMethod().getToken();
        methodHeaderSpan = new Span(
                methodStart.getLine(),
                firstTokenAfterHeader.getLine(),
                methodStart.getCharPositionInLine(),
                firstTokenAfterHeader.getCharPositionInLine() - 1);
    }

    @Override
    public Collection<String> handleToken(Token token, Collection<String> syntaxClasses) {
        if (tokenInSpan(methodHeaderSpan, token)) {
            return syntaxClasses;
        } else if (tokenInOneSpan(assignmentSpans, token)) {
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

    private boolean isPositiveGuard(PathConditionElement pathConditionElement) {
        return pathConditionElement.getType() == PathConditionElement.AssumptionType.IF_THEN
                || pathConditionElement.getType() == PathConditionElement.AssumptionType.WHILE_TRUE;
    }

    private boolean isNegativeGuard(PathConditionElement pathConditionElement) {
        return pathConditionElement.getType() == PathConditionElement.AssumptionType.IF_ELSE
                || pathConditionElement.getType() == PathConditionElement.AssumptionType.WHILE_FALSE;
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
        if (between(token.getLine(), span.beginLine, span.endLine)) {
            return true;
        } else if (token.getLine() == span.beginLine) {
            return token.getCharPositionInLine() >= span.beginCharInLine;
        } else if (token.getLine() == span.endLine) {
            return (token.getCharPositionInLine() + token.getText().length()) <= span.endCharInLine;
        }
        return false;
    }

    private boolean between(int n, int low, int high) {
        return low < n && n < high;
    }

}
