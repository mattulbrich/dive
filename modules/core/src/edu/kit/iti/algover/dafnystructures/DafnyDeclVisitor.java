package edu.kit.iti.algover.dafnystructures;

/**
 * Created by sarah on 10/20/16.
 */
public interface DafnyDeclVisitor<R, A> {
    R visitDefault(DafnyDecl d, A arg);
    R visit(DafnyClass cl, A arg);
    R visit(DafnyMethod m, A arg);
    R visit(DafnyFunction f, A arg);
    R visit(DafnyField fi, A arg);


}
