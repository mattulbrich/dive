/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */

package edu.kit.iti.algover.parser;

import edu.kit.iti.algover.dafnystructures.DafnyFile;
import edu.kit.iti.algover.project.Project;

public class SyntacticSugarVistor {

    public static void visitProject(Project project) {
        // TODO Auto-generated method stub

        // a < b < c

        // var i, j : int

        // var i := 0

        for (DafnyFile df : project.getDafnyFiles()) {
            df.getRepresentation().accept(new ParameterContractionVisitor(), null);
        }
    }


}
