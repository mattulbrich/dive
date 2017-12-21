package edu.kit.iti.algover.util;

import javafx.beans.property.ObjectProperty;
import javafx.beans.property.SimpleObjectProperty;

import java.util.function.Consumer;
import java.util.function.Function;

public class SubSelection<S> {

    private final ObjectProperty<S> selected;
    private final Consumer<S> onUpdateListener;

    public SubSelection(Consumer<S> onUpdateListener) {
        this((S) null, onUpdateListener);
    }

    public SubSelection(S initial, Consumer<S> onUpdateListener) {
        this(new SimpleObjectProperty<>(initial), onUpdateListener);
    }

    public SubSelection(ObjectProperty<S> selected, Consumer<S> onUpdateListener) {
        this.selected = selected;
        this.onUpdateListener = onUpdateListener;
    }

    public <Sub> SubSelection<Sub> subSelection(Function<S, Sub> updateInner, Function<Sub, S> updateOuter) {
        final Function<S, Sub> nullHandlingInner = mapNull(updateInner);
        final Function<Sub, S> nullHandlingOuter = mapNull(updateOuter);

        ObjectProperty<Sub> subProperty = BindingsUtil.convert(nullHandlingInner, selected);
        return new SubSelection<Sub>(subProperty, inner -> select(nullHandlingOuter.apply(inner)));
    }

    public ObjectProperty<S> selected() {
        return selected;
    }

    public void select(S s) {
        selected.set(s);
        onUpdateListener.accept(s);
    }

    public void unsetGobally() {
        select(null);
    }

    private <A, R> Function<A, R> mapNull(Function<A, R> nonNullHandling) {
        return a -> a == null ? null : nonNullHandling.apply(a);
    }

}
