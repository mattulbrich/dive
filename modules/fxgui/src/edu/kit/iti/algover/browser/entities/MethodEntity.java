package edu.kit.iti.algover.browser.entities;

import edu.kit.iti.algover.dafnystructures.DafnyFile;
import edu.kit.iti.algover.dafnystructures.DafnyMethod;

/**
 * Created by philipp on 12.07.17.
 */
public class MethodEntity extends TreeTableEntity {

    private final DafnyMethod dafnyMethod;

    public MethodEntity(DafnyMethod dafnyMethod, DafnyFile location) {
        super(dafnyMethod.getName(), location);
        this.dafnyMethod = dafnyMethod;
    }

    @Override
    public <T> T accept(TreeTableEntityVisitor<T> visitor) {
        return visitor.visitMethod(this);
    }

    public DafnyMethod getDafnyMethod() {
        return dafnyMethod;
    }

}
