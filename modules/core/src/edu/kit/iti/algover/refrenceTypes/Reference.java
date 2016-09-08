package edu.kit.iti.algover.refrenceTypes;

/**
 * Created by sarah on 9/7/16.
 */
public class Reference {
    ReferenceTarget sourceObject;
    ReferenceTarget targetObject;

    public Reference(ReferenceTarget sourceObject, ReferenceTarget targetObject){
        this.sourceObject = sourceObject;
        this.targetObject = targetObject;
    }

}
