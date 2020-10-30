package edu.kit.iti.algover.rules.impl;

import java.util.Collections;
import java.util.HashSet;
import java.util.Set;

public class BoogieCache {

    private final static Set<String> provedConditions =
            Collections.synchronizedSet(new HashSet<>());


    public static boolean contains(String hashCode) {
        return provedConditions.contains(hashCode);
    }

    public static void add(String hashCode) {
        provedConditions.add(hashCode);
    }

}
