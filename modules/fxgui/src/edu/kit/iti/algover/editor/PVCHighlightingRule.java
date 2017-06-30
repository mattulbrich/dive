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

    private final PVC pvc;
    private final List<Token> assignmentTokens;
    private final List<Token> positiveGuardTokens;
    private final List<Token> negativeGuardTokens;
    private final List<Token> allGuardTokens;
    private final List<Token> proofObligationTokens;

    public PVCHighlightingRule(PVC pvc) {
        this.pvc = pvc;


        SymbexPath symbexPath = pvc.getPathThroughProgram();

        List<DafnyTree> assignmentsAsList = new ArrayList<>();
        symbexPath.getAssignmentHistory().forEach(assignmentsAsList::add);
        assignmentTokens =
                assignmentsAsList.stream()
                        .flatMap(dafnyTree -> collectTokens(dafnyTree).stream())
                        .collect(Collectors.toList());

        List<PathConditionElement> pathConditionsAsList = new ArrayList<>();
        symbexPath.getPathConditions().forEach(pathConditionsAsList::add);

        positiveGuardTokens = pathConditionsAsList.stream()
                .filter(pathConditionElement -> pathConditionElement.getType() == PathConditionElement.AssumptionType.IF_THEN)
                .flatMap(pathConditionElement -> collectTokens(pathConditionElement.getExpression()).stream())
                .collect(Collectors.toList());

        negativeGuardTokens = pathConditionsAsList.stream()
                .filter(pathConditionElement -> pathConditionElement.getType() == PathConditionElement.AssumptionType.IF_ELSE)
                .flatMap(pathConditionElement -> collectTokens(pathConditionElement.getExpression()).stream())
                .collect(Collectors.toList());

        allGuardTokens = pathConditionsAsList.stream()
                .flatMap(pathConditionElement -> collectTokens(pathConditionElement.getExpression()).stream())
                .collect(Collectors.toList());

        List<AssertionElement> proofObligationsAsList = new ArrayList<>();
        symbexPath.getProofObligations().forEach(proofObligationsAsList::add);
        proofObligationTokens = proofObligationsAsList.stream()
                .flatMap(assertionElement -> collectTokens(assertionElement.getOrigin()).stream())
                .collect(Collectors.toList());

        // TODO: Find out what the tokens are for a method header. for example for the header
        // "method max(x: int, y: int) returns (m: int) {". That should still be highlighted
    }

    @Override
    public Collection<String> handleToken(Token token, Collection<String> syntaxClasses) {
        if (oneTokenMatches(assignmentTokens, token)) {
            return syntaxClasses;
        } else if (oneTokenMatches(proofObligationTokens, token)) {
            return syntaxClasses;
        } else if (oneTokenMatches(allGuardTokens, token)) {
            if (oneTokenMatches(positiveGuardTokens, token)) {
                return addClass(syntaxClasses, "guard-positive");
            } else if (oneTokenMatches(negativeGuardTokens, token)) {
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

    private boolean oneTokenMatches(List<Token> tokens, Token token) {
        return tokens.stream().anyMatch(specificToken -> tokensMatch(specificToken, token));
    }

    private boolean tokensMatch(Token asgnToken, Token token) {
        return asgnToken.getLine() == token.getLine() && asgnToken.getCharPositionInLine() == token.getCharPositionInLine();
    }

    private List<Token> collectTokens(DafnyTree tree) {
        List<Token> tokens = new ArrayList<>();
        collectTokensTo(tokens, tree);
        return tokens;
    }

    private void collectTokensTo(List<Token> list, DafnyTree tree) {
        list.add(tree.getToken());
        tree.getChildren().forEach(subTree -> collectTokensTo(list, subTree));
    }
}
