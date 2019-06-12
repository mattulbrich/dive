/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 *
 */

package edu.kit.iti.algover.util;

@FunctionalInterface
public interface ConsumerWithException<T, E extends Exception> {
    void accept(T t) throws E;
}
