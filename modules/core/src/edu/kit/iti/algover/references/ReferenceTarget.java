package edu.kit.iti.algover.references;

/**
 * An object that encapsulates the types of reference targets stored as nodes in the reference graph.
 * @author S. Grebing
 */
public abstract class ReferenceTarget {

    public abstract <R> R accept(ReferenceTargetVisitor<R> visitor);

}
