/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.util;

@FunctionalInterface
public interface FunctionWithException<From, To, E extends Exception> {

    To apply(From from) throws E;

}
