package edu.kit.iti.algover.browser.entities;

import edu.kit.iti.algover.dafnystructures.DafnyFile;
import edu.kit.iti.algover.dafnystructures.DafnyFunction;
import edu.kit.iti.algover.dafnystructures.DafnyMethod;

import java.util.List;

/**
 * Created by jklamroth on 8/28/18.
 */
public class FunctionEntity extends TreeTableEntity {

    private final DafnyFunction dafnyFunction;

    public FunctionEntity(DafnyFunction dafnyFunction, DafnyFile location, List<TreeTableEntity> children) {
        super(dafnyFunction.getName(), location, children);
        this.dafnyFunction = dafnyFunction;
    }

    @Override
    public <T> T accept(TreeTableEntityVisitor<T> visitor) {
        return visitor.visitFunction(this);
    }

    public DafnyFunction getDafnyFunction() {
        return dafnyFunction;
    }
}
