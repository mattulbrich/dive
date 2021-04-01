/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.util;

import nonnull.NonNull;
import nonnull.Nullable;

import java.util.LinkedList;
import java.util.List;
import java.util.Objects;

/**
 * A helper class which implements the observer pattern for a single value.
 * Similar to properties in JavaFX, but way more lightweight.
 *
 * Every property has a name and actively knows about its type.
 *
 * Observers are implementations of the functional interface
 * {@link ChangeListener}.
 *
 * @param <T> The type of the value to stored in the property.
 *
 * @author Mattias Ulbrich
 */
public class ObservableValue<T> {

    /**
     * A change listener is invoked whenever a value changes.
     */
    @FunctionalInterface
    public interface ChangeListener<T> {
        /**
         * Invoked when the value of {@code observableValue} changes from {@code oldValue}
         * to {@code newValue}.
         *
         * @param observableValue the observable item that has changed value
         * @param oldValue the old value before changing
         * @param newValue the new value after changing.
         */
        void changed(@NonNull ObservableValue<T> observableValue, @Nullable T oldValue, @Nullable T newValue);
    }

    /** The name of this observable value (mainly for debugging) */
    private final String name;

    /** The type of the value of this observable */
    private final Class<T> type;

    /** The actual value currently stored in the observable */
    private T value;

    /** The list of listeners to be notified when changes arrive */
    private List<ChangeListener<T>> observers;

    /** A lock needed for synchronisation when used with several threads */
    private final Object listLock = new Object();

    /**
     * Some use cases may choose to store the origin of the change.
     * Can be retrieved using {@link #getOrigin()}.
     */
    private Object origin;

    /**
     * Create a new observable value object.
     *
     * @param name name of the observable
     * @param type the class that can be stored in the value
     * @param initialValue the initial value.
     */
    public ObservableValue(@NonNull  String name, @NonNull  Class<T> type, @Nullable T initialValue) {
        this.name = name;
        this.type = type;
        this.value = initialValue;
    }

    /**
     * Create a new observable value object.
     *
     * Initial value is null.
     *
     * @param name name of the observable
     * @param type the class that can be stored in the value
     */
    public ObservableValue(String name, Class<T> type) {
        this(name, type, null);
    }

    public String getName() {
        return name;
    }

    public Class<T> getType() {
        return type;
    }

    public T getValue() {
        return value;
    }

    @Override
    public String toString() {
        return "ObservableValue[" + name + " (" + type + "): " + value + "]";
    }

    public void setValue(T value) {
        setValue(null, value);
    }

    public void setValue(Object origin, T value) {
        this.origin = origin;
        T oldValue = this.value;
        boolean changed = value != this.value && !Objects.equals(value, oldValue);
        this.value = value;
        if(changed) {
            notifyObservers(oldValue);
        }
    }

    public void addObserver(Runnable observer) {
        addObserver((p,o,n) -> observer.run());
    }

    public void addObserver(ChangeListener<T> observer) {
        synchronized (listLock) {
            if (observers == null) {
                observers = new LinkedList<>();
            }
            observers.add(observer);
        }
    }

    public void removeObserver(ChangeListener<T> observer) {
        synchronized (listLock) {
            if(observers != null) {
                observers.remove(observer);
            }
        }
    }

    public Object getOrigin() {
        return origin;
    }

    private void notifyObservers(T oldValue) {
        if(observers != null) {
            T newValue = this.value;
            for (ChangeListener<T> observer : observers) {
                observer.changed(this, oldValue, newValue);
            }
        }
    }
}
