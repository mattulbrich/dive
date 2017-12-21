package edu.kit.iti.algover.editor;

import edu.kit.iti.algover.parser.DafnyTree;
import edu.kit.iti.algover.util.Span;
import org.antlr.runtime.Token;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

public abstract class SpanHighlightingRule implements HighlightingRule {

    protected static Span spanFromToken(Token token) {
        return new Span(
                token.getLine(),
                token.getLine(),
                token.getCharPositionInLine(),
                token.getText() == null
                        ? token.getCharPositionInLine()
                        : token.getText().length() + token.getCharPositionInLine()
        );
    }

    protected static Token minPos(Token token1, Token token2) {
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
    protected static Span spanFromDafnyTree(DafnyTree tree) {
        return spanFromStartEnd(tree.getStartToken(), tree.getStopToken());
    }

    protected static Span spanFromStartEnd(Token startToken, Token endToken) {
        return Span.union(spanFromToken(startToken), spanFromToken(endToken));
    }

    protected Collection<String> addClass(Collection<String> syntaxClasses, String cssClass) {
        List<String> classes = new ArrayList<>();
        classes.addAll(syntaxClasses);
        classes.add(cssClass);
        return classes;
    }

    protected boolean tokenInOneSpan(List<Span> spans, Token token) {
        return spans.stream().anyMatch(span -> tokenInSpan(span, token));
    }

    protected boolean tokenInSpan(Span span, Token token) {
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
