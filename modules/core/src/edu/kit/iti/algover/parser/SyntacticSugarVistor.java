/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */

package edu.kit.iti.algover.parser;

import edu.kit.iti.algover.dafnystructures.DafnyFile;
import edu.kit.iti.algover.project.Project;
import edu.kit.iti.algover.util.LabelIntroducer;

public class SyntacticSugarVistor {

    public static void visitProject(Project project) throws DafnyException {
        // TODO Auto-generated method stub

        // [x] a < b < c

        // [ ] var i, j : int

        // [ ] var i := 0

        // [ ] forall i :: [i]  ... default to int or do inference

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

        // t.accept(new ImplicitlyTypedVariableVisitor(), null);
    }


}
