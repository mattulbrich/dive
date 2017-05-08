/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.symbex;

import edu.kit.iti.algover.parser.DafnyTree;

public class LocalVarDecl {

    private final String name;
    private final DafnyTree type;
    private final DafnyTree reference;

    public LocalVarDecl(String name, DafnyTree type, DafnyTree reference) {
        this.name = name;
        this.type = type;
        this.reference = reference;
    }

    public String getName() {
        return name;
    }

    public DafnyTree getType() {
        return type;
    }

    public DafnyTree getReference() {
        return reference;
    }


}
