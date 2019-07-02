package edu.kit.iti.algover.browser.callvisualization;

import edu.kit.iti.algover.dafnystructures.*;
import edu.kit.iti.algover.parser.DafnyTree;

public class DafnyCallEntityVisitor implements DafnyDeclVisitor<AbstractCallEntity, DafnyTree> {
    private HighlightingHandler listener;
    private boolean call;

    public DafnyCallEntityVisitor(HighlightingHandler listener, boolean call) {
        this.listener = listener;
        this.call = call;
    }

    @Override
    public AbstractCallEntity visit(DafnyClass cl, DafnyTree arg) {
        return null;
    }

    @Override
    public AbstractCallEntity visit(DafnyMethod m, DafnyTree arg) {
        return new DafnyMethodEntity(m, arg, listener);
    }

    @Override
    public AbstractCallEntity visit(DafnyFunction f, DafnyTree arg) {
        return new DafnyFunctionEntity(f, arg, listener, call);
    }

    @Override
    public AbstractCallEntity visit(DafnyField fi, DafnyTree arg) {
        return null;
    }

    @Override
    public AbstractCallEntity visit(DafnyFile file, DafnyTree arg) {
        return null;
    }
}