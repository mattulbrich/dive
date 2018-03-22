package edu.kit.iti.algover.util;

import javafx.concurrent.Task;
import org.fxmisc.richtext.CodeArea;
import org.fxmisc.richtext.model.StyleSpans;

import java.time.Duration;
import java.util.Collection;
import java.util.Optional;
import java.util.concurrent.ExecutorService;

public abstract class AsyncHighlightingCodeArea extends CodeArea {

    private final ExecutorService executor;

    public AsyncHighlightingCodeArea(ExecutorService executor) {
        this.executor = executor;
    }

    protected Task<StyleSpans<Collection<String>>> runAsyncHighlightingTask() {
        final String text = getText();
        Task<StyleSpans<Collection<String>>> task = new Task<StyleSpans<Collection<String>>>() {
            @Override
            protected StyleSpans<Collection<String>> call() throws Exception {
                return computeHighlighting(text);
            }
        };
        executor.execute(task);
        return task;
    }

    protected void setupAsyncSyntaxhighlighting() {
        richChanges()
                .filter(ch -> !ch.getInserted().equals(ch.getRemoved())) // XXX
                .successionEnds(Duration.ofMillis(500))
                .hook(collectionRichTextChange -> getUndoManager().mark())
                .supplyTask(this::runAsyncHighlightingTask)
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
    }

    protected void applyHighlighting(StyleSpans<Collection<String>> styleSpans) {
        setStyleSpans(0, styleSpans);
    }

    protected abstract StyleSpans<Collection<String>> computeHighlighting(String text) throws Exception;
}
