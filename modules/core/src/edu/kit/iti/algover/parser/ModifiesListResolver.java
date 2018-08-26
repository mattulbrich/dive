/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 *
 */

package edu.kit.iti.algover.parser;

import edu.kit.iti.algover.term.Sort;
import edu.kit.iti.algover.util.ASTUtil;
import edu.kit.iti.algover.util.TreeUtil;
import nonnull.NonNull;

import java.util.ArrayList;
import java.util.List;


/**
 * Use this class to resolve the mixed input of modifies clauses.
 *
 * Modifies clauses may contain objects and sets of objects.
 *
 * The resolution works as follows: Neighbouring object references are combined
 * into set extensions. Objects sets are added using set union.
 *
 * @author mulbrich
 */
public class ModifiesListResolver {

    /**
     * Resolves the arguments of a modifies clause.
     *
     * The resulting tree is the translation of the arguments.
     *
     * @param tree the modifies clause to resolve. Its type must be
     * {@link DafnyParser#MODIFIES}.
     * @return a freshly created tree
     * @throws DafnyException if the typing is not correct.
     */
    public static @NonNull DafnyTree resolve(@NonNull DafnyTree tree) throws DafnyException {

        assert tree.getType() == DafnyParser.MODIFIES;

        List<DafnyTree> sets = new ArrayList<>();
        List<DafnyTree> expressions = new ArrayList<>();

        for (DafnyTree child : tree.getChildren()) {
            DafnyTree type = child.getExpressionType();
            Sort sort = TreeUtil.toSort(type);
            if(isReferenceSort(sort)) {
                expressions.add(child);
            } else if(sort.getName().equals("set")) {
                Sort elementSort = sort.getArgument(0);
                if(isReferenceSort(elementSort)) {
                    if(!expressions.isEmpty()) {
                        DafnyTree listEx = ASTUtil.setExt(expressions);
                        sets.add(listEx);
                        expressions.clear();
                    }
                    sets.add(child);
                } else {
                    throw new DafnyException("Unsupported set expression in modifies clause", child);
                }
            } else {
                throw new DafnyException("Unsupported expression in modifies clause", child);
            }
        }

        if(!expressions.isEmpty()) {
            DafnyTree listEx = ASTUtil.setExt(expressions);
            sets.add(listEx);
            expressions.clear();
        }

        return ASTUtil.setUnion(sets);
    }

    private static boolean isReferenceSort(Sort sort) {
        return sort.isSubtypeOf(Sort.OBJECT);
    }
}
