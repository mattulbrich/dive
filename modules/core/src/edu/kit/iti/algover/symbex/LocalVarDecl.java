/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.symbex;

import edu.kit.iti.algover.parser.DafnyTree;
import nonnull.NonNull;

/**
 * A local variable declaration to be used as information about freshly created
 * variables within {@link Symbex}. Stored in {@link SymbexPath}s.
 *
 * @author Mattias Ulbrich
 */
public class LocalVarDecl {

    /**
     * The name of the declared variable.
     */
    private final
    @NonNull
    String name;

    /**
     * The type of the declared variable.
     */
    private final
    @NonNull
    DafnyTree type;

    /**
     * The reference to the corresponding dafny tree declaration.
     */
    private final
    @NonNull
    DafnyTree reference;

    /**
     * Instantiates a new local variable declaration.
     *
     * @param name      the name
     * @param type      the type
     * @param reference the reference
     */
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
