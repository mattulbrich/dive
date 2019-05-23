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
import java.util.function.Consumer;

public class Property<T> {

    private final String name;
    private final Class<T> type;
    private final Object listLock = new Object();

    private T value;
    private List<Consumer<T>> observers;
    private boolean isActive = false;

    public Property(String name, Class<T> type, T value) {
        this.name = name;
        this.type = type;
        this.value = value;
    }

    public Property(String name, Class<T> type) {
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
        boolean changed = value != this.value && !Objects.equals(value, this.value);
        this.value = value;
        if(changed) {
            notifyObservers();
        }
    }

    public void setValueOnEventQueue(T value) {
        if(EventQueue.isDispatchThread()) {
            setValue(value);
        } else {
            SwingUtilities.invokeLater(() -> setValue(value));
        }
    }

    public void addObserver(Runnable observer) {
        addObserver(x -> observer.run());
    }

    public void addObserver(Consumer<T> observer) {
        synchronized (listLock) {
            if(observers == null) {
                observers = new LinkedList<>();
            }
            observers.add(observer);
        }
    }

    public void removeObserver(Object observer) {
        synchronized (listLock) {
            if(observers != null) {
                observers.remove(observer);
            }
        }
    }

    public void notifyObservers() {
        if(observers != null && !isActive) {
            try {
                isActive = true;
                for (Consumer<T> observer : observers) {
                    observer.accept(this.value);
                }
            } finally {
                isActive = false;
            }
        }
    }

}
