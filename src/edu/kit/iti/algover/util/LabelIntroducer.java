/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.util;

import edu.kit.iti.algover.parser.DafnyParser;
import edu.kit.iti.algover.parser.DafnyTree;

public class LabelIntroducer {

    public void visit(DafnyTree tree) {
        if(tree == null) {
            return;
        }

        if(tree.getType() == DafnyParser.INVARIANT) {
            DafnyTree label = tree.getFirstChildWithType(DafnyParser.LABEL);
            if(label == null) {
//                DafnyTree parent = tree.getParent();

            }
        }
    }

}
