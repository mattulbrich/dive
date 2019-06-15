/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.references;

/**
 * An object that encapsulates the types of reference targets
 * Created by sarah on 9/6/16.
 */
public abstract class Reference {

    public abstract <R> R accept(ReferenceVisitor<R> visitor);

}
