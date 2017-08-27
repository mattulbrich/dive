package edu.kit.iti.algover.refrenceTypes;

/**
 * An object that encapsulates the types of reference targets
 * Created by sarah on 9/6/16.
 */
public abstract class ReferenceTarget {

    public abstract <R> R accept(ReferenceTargetVisitor<R> visitor);

}
