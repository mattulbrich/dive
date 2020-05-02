/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.parser;

import edu.kit.iti.algover.term.Sort;
import edu.kit.iti.algover.util.ASTUtil;
import edu.kit.iti.algover.util.TreeUtil;
import nonnull.NonNull;

import java.util.ArrayList;
import java.util.Collections;
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

    private static final DafnyTree SET_OBJ = setObject();

    private static DafnyTree setObject() {
        DafnyTree result = new DafnyTree(DafnyParser.SET, "set");
        result.addChild(new DafnyTree(DafnyParser.OBJECT, "object"));
        return result;
    }

    /**
     * Resolves the arguments of a modifies or reads clause.
     *
     * The resulting tree is the translation of the arguments as set expression
     *
     * @param tree the modifies clause to resolve. Its type must be {@link
     *             DafnyParser#MODIFIES}.
     * @return a freshly created tree
     * @throws DafnyException if the typing is not correct.
     */
    public static @NonNull DafnyTree resolve(@NonNull DafnyTree tree) throws DafnyException {

        assert List.of(DafnyParser.MODIFIES, DafnyParser.READS).contains(tree.getType());

        List<DafnyTree> sets = new ArrayList<>();
        List<DafnyTree> expressions = new ArrayList<>();

        for (DafnyTree child : tree.getChildren()) {
            DafnyTree type = child.getExpressionType();
            Sort sort = TreeUtil.toSort(type);
            if (isReferenceSort(sort)) {
                expressions.add(child);
            } else if (sort.getName().equals("set")) {
                Sort elementSort = sort.getArgument(0);
                if (isReferenceSort(elementSort)) {
                    if (!expressions.isEmpty()) {
                        DafnyTree listEx = ASTUtil.setExt(expressions);
                        listEx.setExpressionType(SET_OBJ.dupTree());
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

        if (!expressions.isEmpty()) {
            DafnyTree listEx = ASTUtil.setExt(expressions);
            listEx.setExpressionType(SET_OBJ.dupTree());
            sets.add(listEx);
            expressions.clear();
        }

        if (sets.isEmpty()) {
            DafnyTree listEx = ASTUtil.setExt(expressions);
            listEx.setExpressionType(SET_OBJ.dupTree());
            return listEx;
        }

        DafnyTree result = sets.get(0);
        for (int i = 1; i < sets.size(); i++) {
            DafnyTree t = new DafnyTree(DafnyParser.PLUS);
            t.addChild(result);
            t.addChild(sets.get(i));
            t.setExpressionType(SET_OBJ.dupTree());
            result = t;
        }

        return result;
    }

    private static boolean isReferenceSort(Sort sort) {
        return sort.isSubtypeOf(Sort.OBJECT);
    }

}