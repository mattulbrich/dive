package edu.kit.iti.algover.util;

import javafx.beans.property.ObjectProperty;

import java.util.function.Function;

/**
 * This class provides the possibility to bind arbitrarily typed ObjectProperties
 */
public class TypedBindings {
    //allows for some debug output of created bindings
    static private boolean debug = false;

    /**
     * This method allows to create a bidirectional binding between two ObjectProperties.
     *
     * @param a First property (of type A)
     * @param b Second property (of type B)
     * @param aToB A function to convert a value of type A to a value of type B
     * @param bToA A function to convert a value of type B to a value of type A
     * @param <A> the type of the first ObjectProperty
     * @param <B> the type of the second ObjectProperty
     */
    static public <A extends Object, B extends Object> void bind(ObjectProperty<A> a, ObjectProperty<B> b, Function<A, B> aToB, Function<B, A> bToA) {
        if(debug) {
            System.out.println("bind " + a + " and " + b);
        }
        if(a == null || b == null) {
            throw new RuntimeException("Cannot bind property that is null.");
        }
        a.addListener(((observable, oldValue, newValue) -> {
            if(debug) {
                System.out.println("observable = " + observable);
            }
            B newB = aToB.apply(a.get());
            if(newB == null) {
                if(b != null)
                    b.setValue(null);
            } else {
                if (!newB.equals(b.get())) {
                    b.set(newB);
                    if(debug) {
                        System.out.println("new value for " + b + ": " + newB);
                    }
                }
            }
        }));
        b.addListener(((observable, oldValue, newValue) -> {
            if(debug) {
                System.out.println("observable = " + observable);
            }
           A newA = bToA.apply(newValue);
            if(newA == null) {
                if(a != null)
                    a.setValue(null);
            } else {
                if (!newA.equals(a.get())) {
                    a.set(newA);
                    if(debug) {
                        System.out.println("new value for " + a + ": " + newA);
                    }
                }
            }
        }));
    }
}
