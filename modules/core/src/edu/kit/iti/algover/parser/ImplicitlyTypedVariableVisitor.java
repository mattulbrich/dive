/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 *
 */

package edu.kit.iti.algover.parser;

import edu.kit.iti.algover.util.ASTUtil;

/**
 * This syntactic sugar resolution replaces untyped variables in quantifiers by
 * integer variables.
 *
 * {@code forall i :: phi} is replaced by {@code forall i:int :: phi}.
 *
 * TODO in the far future replace this with type inference ... (probably not here)
 *
 * @author mulbrich
 * @see SyntacticSugarVistor
 */
public class ImplicitlyTypedVariableVisitor extends DafnyTreeDefaultVisitor<Void, Void> {

    @Override
    public Void visitEX(DafnyTree t, Void aVoid) {
        walk(t);
        return null;
    }

    @Override
    public Void visitALL(DafnyTree t, Void aVoid) {
        walk(t);
        return null;
    }

    public void walk(DafnyTree tree) {
        DafnyTree type = tree.getFirstChildWithType(DafnyParser.TYPE);
        if(type == null) {
            // TODO in the far future replace this with type inference ... (probably not here)
            tree.insertChild(tree.getChildCount() - 1, ASTUtil.type(new DafnyTree(DafnyParser.INT, "int")));
        }
    }
}
