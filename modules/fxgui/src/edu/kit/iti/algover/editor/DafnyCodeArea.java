package edu.kit.iti.algover.editor;

import edu.kit.iti.algover.AlgoVerApplication;
import edu.kit.iti.algover.parser.DafnyLexer;
import javafx.application.Platform;
import javafx.concurrent.Task;
import org.antlr.runtime.ANTLRStringStream;
import org.antlr.runtime.Token;
import org.fxmisc.richtext.CodeArea;
import org.fxmisc.richtext.LineNumberFactory;
import org.fxmisc.richtext.StyleSpans;
import org.fxmisc.richtext.StyleSpansBuilder;

import java.time.Duration;
import java.util.Collection;
import java.util.Collections;
import java.util.Optional;

/**
 * Created by philipp on 28.06.17.
 */
public class DafnyCodeArea extends CodeArea {

    private HighlightingRule highlightingRule;

    public DafnyCodeArea(String text) {
        this.highlightingRule = (token, syntaxClasses) -> syntaxClasses;
        getStylesheets().add(DafnyCodeArea.class.getResource("dafny-keywords.css").toExternalForm());
        setParagraphGraphicFactory(LineNumberFactory.get(this));
        setupAsyncSyntaxhighlighting(text);
    }

    private void setupAsyncSyntaxhighlighting(String initialText) {
        richChanges()
            .filter(ch -> !ch.getInserted().equals(ch.getRemoved())) // XXX
            .successionEnds(Duration.ofMillis(500))
            .hook(collectionRichTextChange -> getUndoManager().mark())
            .supplyTask(this::computeHighlightingAsync)
            .awaitLatest(richChanges())
            .filterMap(t -> {
                if (t.isSuccess()) {
                    return Optional.of(t.get());
                } else {
                    t.getFailure().printStackTrace();
                    return Optional.empty();
                }
            })
            .subscribe(this::applyHighlighting);
        replaceText(0, 0, initialText);
        getUndoManager().forgetHistory();
    }

    public void rerenderHighlighting() {
        Task<StyleSpans<Collection<String>>> task = computeHighlightingAsync();
        task.setOnSucceeded(event -> {
            final StyleSpans<Collection<String>> styleSpans = task.getValue();
            Platform.runLater(() -> applyHighlighting(styleSpans));
        });
    }

    private Task<StyleSpans<Collection<String>>> computeHighlightingAsync() {
        final String text = getText();
        Task<StyleSpans<Collection<String>>> task = new Task<StyleSpans<Collection<String>>>() {
            @Override
            protected StyleSpans<Collection<String>> call() throws Exception {
                return computeHighlighting(text);
            }
        };
        AlgoVerApplication.SH_EXECUTOR.execute(task);
        return task;
    }

    // This method should always run asynchronously to the javafx event thread
    private StyleSpans<Collection<String>> computeHighlighting(String text) {
        StyleSpansBuilder<Collection<String>> builder = new StyleSpansBuilder<>();

        if (text.isEmpty()) {
            builder.add(Collections.emptyList(), 0);
            return builder.create();
        }

        DafnyLexer lexer = new DafnyLexer(new ANTLRStringStream(text));

        Token token;
        while ((token = lexer.nextToken()).getType() != Token.EOF) {
            builder.add(
                highlightingRule.handleToken(
                    token,
                    styleClassForToken(token.getType())),
                token.getText().length());
        }

        return builder.create();
    }

    private Collection<String> styleClassForToken(int type) {
        switch (type) {
            case DafnyLexer.METHOD:
            case DafnyLexer.CLASS:
            case DafnyLexer.VAR:
            case DafnyLexer.IF:
            case DafnyLexer.ELSE:
            case DafnyLexer.RETURNS:
            case DafnyLexer.WHILE:
            case DafnyLexer.FUNCTION:
            case DafnyLexer.ASSIGN:
            case DafnyLexer.RETURN:
                return Collections.singletonList("code-keyword");
            case DafnyLexer.REQUIRES:
            case DafnyLexer.ENSURES:
            case DafnyLexer.INVARIANT:
            case DafnyLexer.DECREASES:
            case DafnyLexer.ASSERT:
            case DafnyLexer.MODIFIES:
            case DafnyLexer.LEMMA:
                return Collections.singleton("specification-keyword");
            case DafnyLexer.MULTILINE_COMMENT:
            case DafnyLexer.SINGLELINE_COMMENT:
                return Collections.singleton("comment");
            case DafnyLexer.INT:
            case DafnyLexer.BOOL:
            case DafnyLexer.SEQ:
            case DafnyLexer.SET:
            case DafnyLexer.ARRAY:
                return Collections.singleton("type-literal");
            case DafnyLexer.INT_LIT:
            case DafnyLexer.TRUE:
            case DafnyLexer.FALSE:
                return Collections.singleton("value-literal");
            default:
                return Collections.emptyList();
        }
    }

    private void applyHighlighting(StyleSpans<Collection<String>> styleSpans) {
        setStyleSpans(0, styleSpans);
    }

    public HighlightingRule getHighlightingRule() {
        return highlightingRule;
    }

    public void setHighlightingRule(HighlightingRule highlightingRule) {
        if (highlightingRule == null) {
            this.highlightingRule = (token, syntaxClasses) -> syntaxClasses;
        } else {
            this.highlightingRule = highlightingRule;
        }
    }
}