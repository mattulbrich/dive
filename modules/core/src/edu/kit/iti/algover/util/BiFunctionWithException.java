/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 */

package edu.kit.iti.algover.util;

@FunctionalInterface
public interface BiFunctionWithException<From1, From2, To, E extends Exception> {

    To apply(From1 a, From2 b) throws E;

}
