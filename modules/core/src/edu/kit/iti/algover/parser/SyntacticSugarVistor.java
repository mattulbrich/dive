/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */

package edu.kit.iti.algover.parser;

import edu.kit.iti.algover.dafnystructures.DafnyFile;
import edu.kit.iti.algover.project.Project;
import edu.kit.iti.algover.util.LabelIntroducer;

import java.util.Arrays;
import java.util.Collections;
import java.util.List;

/**
 * This class collects all routines that resolve syntactic sugar.
 * These are syntactical conveniance aspects and technical afterprocessing steps.
 *
 * <h2>Syntactic sugar</h2>
 * <ul>
 *     <li>{@code a < b < c} is dealt with by {@link ChainedRelationsVisitor}</li>
 *     <li>{@code forall i:int | phi :: psi} is dealt with by {@link QuantifierGuardRemovalVisitor}</li>
 *     <li>{@code forall i :: phi} is dealt with by {@link ImplicitlyTypedVariableVisitor}</li>
 * </ul>
 *
 * TODO Do not iterate n times over the tree. See branch muSyntaxSugar.
 *
 * @author mulbrich
 */
public class SyntacticSugarVistor {

    public static void visitProject(Project project) throws DafnyException {

        // [x] forall i :: [i]  ... default to int
        // [ ] or better do inference

        for (DafnyFile df : project.getDafnyFiles()) {
            visit(df.getRepresentation());
        }
    }

    public static void visit(DafnyTree t) throws DafnyException {

        List<DafnyTreeVisitor<?,?>> visitors =
                Arrays.asList(new ParameterContractionVisitor(),
                    // deactivating the label introduction for the moment.
                    // new LabelIntroducer()
                    new ChainedRelationsVisitor(),
                    new QuantifierGuardRemovalVisitor(),
                    new ImplicitlyTypedVariableVisitor());

        visitDeep(t, visitors);
    }

    public static void visitDeep(DafnyTree t, DafnyTreeVisitor<?, ?> visitor) throws DafnyException {
        visitDeep(t, Collections.singletonList(visitor));
    }

    public static void visitDeep(DafnyTree tree, List<DafnyTreeVisitor<?,?>> visitors) throws DafnyException {
        for (DafnyTreeVisitor<?, ?> visitor : visitors) {
            Object result = tree.accept(visitor, null);
            if (result instanceof DafnyException) {
                DafnyException exception = (DafnyException) result;
                throw exception;
            }
            if (result instanceof DafnyTree) {
                DafnyTree newTree = (DafnyTree) result;
                tree = newTree;
            }
        }

        for (DafnyTree child : tree.getChildren()) {
            visitDeep(child, visitors);
        }
    }

}
