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

        // a < b < c

        // var i, j : int

        // var i := 0

        for (DafnyFile df : project.getDafnyFiles()) {
            visit(df.getRepresentation());
        }
    }

    public static void visit(DafnyTree t) throws DafnyException {
        t.accept(new ParameterContractionVisitor(), null);
        t.accept(new LabelIntroducer(), null);
        new ChainedRelationsVisitor().walk(t);
    }


}
