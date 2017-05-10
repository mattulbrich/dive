/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.parser;

import edu.kit.iti.algover.dafnystructures.DafnyClass;
import edu.kit.iti.algover.project.Project;

public class XXXProjectAccess {

    private Project project;

    public XXXProjectAccess(Project project) {
        this.project = project;
    }

    public DafnyClass getClass(String classname) {
        for (DafnyClass c : project.getClasses()) {
            if(c.getName().equals(classname)) {
                return c;
            }
        }
        return null;
    }

}
