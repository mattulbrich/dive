package edu.kit.iti.algover.swing.util;

import javax.swing.*;
import java.awt.*;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.lang.reflect.Method;
import java.lang.reflect.Modifier;
import java.util.LinkedList;
import java.util.List;
import java.util.Objects;
import java.util.function.BiConsumer;
import java.util.function.Consumer;

public class Property<T> implements Signal<T> {

    private final String name;
    private final Class<T> type;
    private final Object listLock = new Object();

    private T value;
    private List<BiConsumer<? super T, ? super T>> observers;
    private boolean isActive = false;

    public Property(String name, Class<T> type, T value) {
        this.name = name;
        this.type = type;
        this.value = value;
    }

    public Property(String name, Class<T> type) {
        this(name, type, null);
    }

    @Override
    public String getName() {
        return name;
    }

    @Override
    public Class<T> getType() {
        return type;
    }

    public T getValue() {
        return value;
    }

    public String exportString() {
        if(value == null) {
            return "(null)";
        } else {
            String string = value.toString();
            if(string.charAt(0) == '#') {
                string = "#" + string;
            }
            return string;
        }
    }

    @Override
    public String toString() {
        return exportString();
    }

    public void setValue(T value) {
        T oldValue = this.value;
        boolean changed = value != oldValue && !Objects.equals(value, oldValue);
        this.value = value;
        if(changed) {
            notifyObservers(oldValue);
        }
    }

    @Override
    public void fire(T value) {
        T oldValue = this.value;
        this.value = value;
        notifyObservers(oldValue);
    }

    public void setValueOnEventQueue(T value) {
        if(EventQueue.isDispatchThread()) {
            setValue(value);
        } else {
            SwingUtilities.invokeLater(() -> setValue(value));
        }
    }

    @Override
    public void addObserver(Runnable observer) {
        addObserver((_old, _new) -> observer.run());
    }

    @Override
    public void addObserver(Consumer<? super T> observer) {
        addObserver((_old, _new) -> observer.accept(_new));
    }

    public void addObserver(BiConsumer<? super T, ? super T> observer) {
        synchronized (listLock) {
            if(observers == null) {
                observers = new LinkedList<>();
            }
            observers.add(observer);
        }
    }

    @Override
    public void removeObserver(Object observer) {
        synchronized (listLock) {
            if(observers != null) {
                observers.remove(observer);
            }
        }
    }

    protected void notifyObservers(T oldValue) {
        if(observers != null && !isActive) {
            try {
                isActive = true;
                for (BiConsumer<? super T, ? super T> observer : observers) {
                    try {
                        observer.accept(oldValue, this.value);
                    } catch (Exception e) {
                        System.err.println("Exception during notification for " + getName());
                        e.printStackTrace();
                    }
                }
            } finally {
                isActive = false;
            }
        }
    }

}
