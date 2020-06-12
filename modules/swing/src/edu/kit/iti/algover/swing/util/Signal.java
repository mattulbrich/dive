package edu.kit.iti.algover.swing.util;

import java.util.List;
import java.util.function.BiConsumer;
import java.util.function.Consumer;

public interface Signal<T> {

    static <T> Signal<T> newSignal(String name, Class<T> argumentType) {
        return new Property<>(name, argumentType);
    }

    String getName();

    Class<T> getType();

    void fire(T value);

    void addObserver(Runnable observer);

    void addObserver(Consumer<? super T> observer);

    void removeObserver(Object observer);
}
