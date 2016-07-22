/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2016 Karlsruhe Institute of Technology
 */
package de.matul.lightup;

import java.awt.Color;
import java.beans.PropertyChangeListener;
import java.beans.PropertyChangeSupport;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.concurrent.atomic.AtomicInteger;

public class LightupConnection {

    private static final AtomicInteger COUNTER = new AtomicInteger();

    public static final Property<Color> COLOR_PROPERTY =
            new Property<Color>("color", Color.class);

    public static final Property<Color> BG_COLOR_PROPERTY =
            new Property<Color>("bgcolor", Color.class);

    private LightupElement from;
    private LightupElement to;
    private int id;

    private List<MovingTarget> movingTargets;
    private Map<Property<?>, Object> properties;
    private PropertyChangeSupport propertySupport;

    public LightupConnection(LightupElement from, LightupElement to) {
        this.from = from;
        this.to = to;
        this.id = COUNTER.incrementAndGet();
    }

    public LightupElement getFrom() {
        return from;
    }

    public void setFrom(LightupElement from) {
        this.from = from;
    }

    public LightupElement getTo() {
        return to;
    }

    public void setTo(LightupElement to) {
        this.to = to;
    }

    public Color getColor() {
        return getProperty(COLOR_PROPERTY);
    }

    public void setColor(Color color) {
        this.setProperty(COLOR_PROPERTY, color);
    }

    public int getId() {
        return id;
    }

    public void setId(int id) {
        this.id = id;
    }

    public void addMovingTarget(MovingTarget target) {
        movingTargets.add(target);
    }

    public void addPropertyChangeListener(PropertyChangeListener listener) {
        propertySupport.addPropertyChangeListener(listener);
    }

    public void addPropertyChangeListener(String propertyName,
            PropertyChangeListener listener) {
        propertySupport.addPropertyChangeListener(propertyName, listener);
    }

    // javafx has own property support! use that!
    public <T> void setProperty(Property<T> prop, T value) {
        Object oldValue;
        if(value == null) {
            if(properties == null) {
                // no need to do anything
                return;
            }
            oldValue = properties.remove(prop);
        } else {
            ensurePropertiesExist();
            oldValue = properties.put(prop, prop.cast(value));
        }

        propertySupport.firePropertyChange(prop.toString(), oldValue, value);
    }

    private void ensurePropertiesExist() {
        if(properties == null) {
            synchronized (this) {
                if(properties == null) {
                    properties = Collections.synchronizedMap(new HashMap<Property<?>, Object>());
                    propertySupport = new PropertyChangeSupport(this);
                }
            }
        }
    }

    public <T> T getProperty(Property<T> prop) {
        if(properties == null) {
            return null;
        }
        return prop.cast(properties.get(prop));
    }

    @Override
    public String toString() {
        return "LightupConnection [from=" + from + ", to=" + to + ", id=" + id
                + ", properties=" + properties + "]";
    }



}
