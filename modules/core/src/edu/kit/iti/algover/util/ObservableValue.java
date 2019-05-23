/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.util;

import java.util.LinkedList;
import java.util.List;
import java.util.Objects;

public class ObservableValue<T> {

    @FunctionalInterface
    public interface ChangeListener<T> {
        void changed(ObservableValue<T> observableValue, T oldValue, T newValue);
    }

    private final String name;
    private final Class<T> type;

    private T value;
    private List<ChangeListener<T>> observers;

    private final Object listLock = new Object();

    private Object origin;

    public ObservableValue(String name, Class<T> type, T initialValue) {
        this.name = name;
        this.type = type;
        this.value = initialValue;
    }

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
        if(observers == null) {
            synchronized (listLock) {
                if(observers == null) {
                    observers = new LinkedList<ChangeListener<T>>();
                }
            }
        }
        observers.add(observer);
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
