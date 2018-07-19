/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */

package edu.kit.iti.algover.parser;

import edu.kit.iti.algover.dafnystructures.DafnyFile;
import edu.kit.iti.algover.project.Project;
import edu.kit.iti.algover.util.LabelIntroducer;

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

        // that is a technical transformation
        t.accept(new ParameterContractionVisitor(), null);

        // deactivating the label introduction for the moment.
        // t.accept(new LabelIntroducer(), null);

        new ChainedRelationsVisitor().walk(t);
        new QuantifierGuardRemovalVisitor().walk(t);
        new ImplicitlyTypedVariableVisitor().walk(t);
    }


}
