/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.parser;

import java.util.List;

import edu.kit.iti.algover.term.Sort;

public class TypeResolution extends DafnyTreeDefaultVisitor<Sort, Void> {

    private List<DafnyException> exceptions;

    public TypeResolution(List<DafnyException> exceptions) {
        this.exceptions = exceptions;
    }

}
