package edu.kit.iti.algover.refrenceTypes;

import java.util.HashSet;
import java.util.Set;

/**
 * Created by Philipp on 27.08.2017.
 */
public class ReferenceSet {

    private final Set<Reference> references;

    public ReferenceSet() {
        references = new HashSet<>();
    }

    public void addReference(ReferenceTarget source, ReferenceTarget target) {
        references.add(new Reference(source, target));
    }

}
