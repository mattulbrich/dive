package edu.kit.iti.algover.editor;

import edu.kit.iti.algover.parser.DafnyParser;
import edu.kit.iti.algover.parser.DafnyTree;
import edu.kit.iti.algover.proof.PVC;
import edu.kit.iti.algover.symbex.AssertionElement;
import edu.kit.iti.algover.symbex.PathConditionElement;
import edu.kit.iti.algover.symbex.SymbexPath;
import edu.kit.iti.algover.util.Span;
import org.antlr.runtime.Token;

import java.util.*;
import java.util.stream.Collectors;

/**
 * Created by philipp on 30.06.17.
 */
public class PVCHighlightingRule extends SpanHighlightingRule {

    private final List<Span> assignmentSpans;
    private final List<Span> positiveGuardSpans;
    private final List<Span> negativeGuardSpans;
    private final List<Span> allGuardSpans;
    private final List<Span> proofObligationSpans;
    private final Span methodHeaderSpan;

    public PVCHighlightingRule(PVC pvc) {
        // REVIEW: Caution! I changed getPathThroughProgram() to Nullable the other day.
        SymbexPath symbexPath = pvc.getPathThroughProgram();

        List<DafnyTree> assignmentsAsList = new ArrayList<>();
        symbexPath.getAssignmentHistory().forEach(assignmentsAsList::add);
        assignmentSpans =
                assignmentsAsList.stream()
                        .map(SpanHighlightingRule::spanFromDafnyTree)
                        .collect(Collectors.toList());

        List<PathConditionElement> pathConditionsAsList = new ArrayList<>();
        symbexPath.getPathConditions().forEach(pathConditionsAsList::add);

        positiveGuardSpans = pathConditionsAsList.stream()
                .filter(this::isPositiveGuard)
                .map(PathConditionElement::getExpression)
                .map(SpanHighlightingRule::spanFromDafnyTree)
                .collect(Collectors.toList());

        negativeGuardSpans = pathConditionsAsList.stream()
                .filter(this::isNegativeGuard)
                .map(PathConditionElement::getExpression)
                .map(SpanHighlightingRule::spanFromDafnyTree)
                .collect(Collectors.toList());

        allGuardSpans = pathConditionsAsList.stream()
                .map(PathConditionElement::getExpression)
                .map(SpanHighlightingRule::spanFromDafnyTree)
                .collect(Collectors.toList());

        List<AssertionElement> proofObligationsAsList = new ArrayList<>();
        symbexPath.getProofObligations().forEach(proofObligationsAsList::add);
        proofObligationSpans = proofObligationsAsList.stream()
                .map(AssertionElement::getOrigin)
                .map(SpanHighlightingRule::spanFromDafnyTree)
                .collect(Collectors.toList());

        List<DafnyTree> treesAfterMethodHeader = new ArrayList<>();
        treesAfterMethodHeader.add(symbexPath.getMethod().getFirstChildWithType(DafnyParser.REQUIRES));
        treesAfterMethodHeader.add(symbexPath.getMethod().getFirstChildWithType(DafnyParser.ENSURES));
        treesAfterMethodHeader.add(symbexPath.getMethod().getFirstChildWithType(DafnyParser.DECREASES));
        treesAfterMethodHeader.add(symbexPath.getMethod().getFirstChildWithType(DafnyParser.BLOCK));


        Token firstTokenAfterHeader = treesAfterMethodHeader.stream()
                .filter(Objects::nonNull)
                .map(DafnyTree::getStartToken)
                .reduce(SpanHighlightingRule::minPos)
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

}
