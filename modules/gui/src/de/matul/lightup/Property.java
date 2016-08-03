/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2016 Karlsruhe Institute of Technology
 */

package de.matul.lightup;

public class Property<T> {

    private String name;
    private Class<T> clazz;

    public Property(String name, Class<T> type) {
        this.name = name;
        this.clazz = type;
    }

    public T cast(Object o) {
        return clazz.cast(o);
    }

    @Override
    public String toString() {
        return name;
    }
}
