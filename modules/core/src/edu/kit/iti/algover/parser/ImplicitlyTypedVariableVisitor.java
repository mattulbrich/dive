/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 *
 */

package edu.kit.iti.algover.parser;

import edu.kit.iti.algover.util.ASTUtil;

public class ImplicitlyTypedVariableVisitor {

    public void walk(DafnyTree tree) {

        switch (tree.getType()) {
        case DafnyParser.ALL:
        case DafnyParser.EX:
            DafnyTree type = tree.getFirstChildWithType(DafnyParser.TYPE);
            if(type == null) {
                // TODO in the far future replace this with type inference ... (probably not here)
                tree.insertChild(tree.getChildCount() - 1, ASTUtil.type("int"));
            }
        }

        tree.getChildren().forEach(this::walk);
    }
}
