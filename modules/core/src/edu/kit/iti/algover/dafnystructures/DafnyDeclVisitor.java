/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.dafnystructures;

/**
 * A visitor pattern for dafny declarations.
 *
 * @author Created by sarah on 10/20/16.
 * @param <R> the type for the result of the visitation
 * @param <A> the type of the argument for the visitation
 */
public interface DafnyDeclVisitor<R, A> {
    // Checkstyle: OFF JavadocMethod

    // REVIEW: Why is there this method? Is it ever referenced? Suggest to remove
    R visitDefault(DafnyDecl d, A arg);
    R visit(DafnyClass cl, A arg);
    R visit(DafnyMethod m, A arg);
    R visit(DafnyFunction f, A arg);
    R visit(DafnyField fi, A arg);
    R visit(DafnyDecl file, A arg);
}