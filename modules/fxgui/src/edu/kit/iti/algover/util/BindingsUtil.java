package edu.kit.iti.algover.util;

import javafx.beans.property.ObjectProperty;
import javafx.beans.property.SimpleObjectProperty;

import java.util.function.Function;

public final class BindingsUtil {

    private BindingsUtil() {
    }

    public static <A, B> ObjectProperty<B> convert(Function<A, B> converter, ObjectProperty<A> origin) {
        ObjectProperty<B> converted = new SimpleObjectProperty<>(converter.apply(origin.get()));
        origin.addListener((observableValue, before, newValue) -> {
            converted.set(converter.apply(newValue));
        });
        return converted;
    }
}
