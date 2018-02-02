/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 */

package edu.kit.iti.algover.util;

@FunctionalInterface
public interface FunctionWithException<From, To, E extends Exception> {

    To apply(From from) throws E;

}
