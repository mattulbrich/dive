package edu.kit.iti.algover.browser.entities;

import edu.kit.iti.algover.dafnystructures.DafnyClass;
import edu.kit.iti.algover.dafnystructures.DafnyFile;

/**
 * Created by philipp on 12.07.17.
 */
public class ClassEntity extends TreeTableEntity {

    private final DafnyClass dafnyClass;

    public ClassEntity(DafnyClass dafnyClass, DafnyFile location) {
        super(dafnyClass.getName(), location);
        this.dafnyClass = dafnyClass;
    }

    @Override
    public <T> T accept(TreeTableEntityVisitor<T> visitor) {
        return visitor.visitClass(this);
    }

    public DafnyClass getDafnyClass() {
        return dafnyClass;
    }

}