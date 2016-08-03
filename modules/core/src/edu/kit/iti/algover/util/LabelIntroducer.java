/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2016 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.util;

import java.util.List;

import org.antlr.runtime.CommonToken;

import edu.kit.iti.algover.parser.DafnyParser;
import edu.kit.iti.algover.parser.DafnyTree;

/**
 * This class can be used to add labels to invariants and postconditions which
 * are not named.
 */
public class LabelIntroducer {

    private LabelIntroducer() {
        throw new Error();
    }

    /**
     * Adds labels to invariants and postconditions.
     *
     * Iterates in depth over all nodes and adds artificial labels to invariants
     * and postconditions that are not already labelled.
     *
     * @param tree
     *            a non-<code>null</code> tree object
     */
    public static void visit(DafnyTree tree) {
        if(tree == null) {
            return;
        }

        int type = tree.getType();
        if(type == DafnyParser.INVARIANT || type == DafnyParser.ENSURES) {
            DafnyTree label = tree.getFirstChildWithType(DafnyParser.LABEL);
            if(label == null) {
                DafnyTree parent = (DafnyTree) tree.getParent();
                List<DafnyTree> siblings = parent.getChildrenWithType(type);
                int no = 1;
                for (DafnyTree dafnyTree : siblings) {
                    if(dafnyTree == tree) {
                        break;
                    }
                    no++;
                }

                DafnyTree idTree = new DafnyTree(DafnyParser.ID, "#" + no);
                DafnyTree labelTree = new DafnyTree(DafnyParser.LABEL);
                labelTree.addChild(idTree);

                tree.insertChild(0, labelTree);
            }
        } else {
            if(tree.getChildCount() > 0) {
                // checks is required, NPE otherwise
                for (DafnyTree child : tree.getChildren()) {
                    visit(child);
                }
            }
        }
    }

}
