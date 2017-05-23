/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.parser;

import java.util.ArrayList;
import java.util.List;

import edu.kit.iti.algover.project.Project;

public final class ProjectResolver {

    private ProjectResolver() {
        throw new Error();
    }

    public static List<DafnyException> resolve(Project project) {

        List<DafnyException> excs = new ArrayList<>();

        SyntacticSugarVistor ssv = new SyntacticSugarVistor();
        ssv.visitProject(project);

        ReferenceResolutionVisitor rrv = new ReferenceResolutionVisitor(project, excs);
        rrv.visitProject();

        TypeResolution tr = new TypeResolution(excs);
        tr.visitProject(project);

        return excs;
    }


}
