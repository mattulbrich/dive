package edu.kit.iti.algover.refrenceTypes;

/**
 * An object that encapsulates the types of reference targets
 * Created by sarah on 9/6/16.
 */
public abstract class Reference {

    public abstract <R> R accept(ReferenceVisitor<R> visitor);

}
