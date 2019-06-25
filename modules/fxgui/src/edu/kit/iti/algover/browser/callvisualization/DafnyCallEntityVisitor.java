package edu.kit.iti.algover.browser.callvisualization;

import edu.kit.iti.algover.dafnystructures.*;
import edu.kit.iti.algover.parser.DafnyTree;

public class DafnyCallEntityVisitor implements DafnyDeclVisitor<CallEntity, DafnyTree> {

    @Override
    public CallEntity visit(DafnyClass cl, DafnyTree arg) {
        return null;
    }

    @Override
    public CallEntity visit(DafnyMethod m, DafnyTree arg) {
        return new CallEntity(m, arg);
    }

    @Override
    public CallEntity visit(DafnyFunction f, DafnyTree arg) {
        return new CallEntity(f, arg);
    }

    @Override
    public CallEntity visit(DafnyField fi, DafnyTree arg) {
        return null;
    }

    @Override
    public CallEntity visit(DafnyFile file, DafnyTree arg) {
        return null;
    }
}