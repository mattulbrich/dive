/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.symbex;

import edu.kit.iti.algover.parser.DafnyParser;
import edu.kit.iti.algover.parser.DafnyTree;
import edu.kit.iti.algover.parser.ModifiesListResolver;
import edu.kit.iti.algover.symbex.PathConditionElement.AssumptionType;
import edu.kit.iti.algover.util.ASTUtil;
import edu.kit.iti.algover.util.Util;

import java.util.Deque;
import java.util.LinkedList;
import java.util.List;

/**
 * This short class produces the proof obligations for a function symbol.
 *
 * It delegates the task to {@link SymbexExpressionValidator} for the
 * wellfoundedness and wellformedness questions.
 *
 * It applies a visitor for checking reads clauses.
 */
public class FunctionObligationMaker {

    /**
     * Generate a number of SymbexPaths that correspond to the proof obligations
     * for the given function.
     *
     * @param function object to analyse
     * @return a fresh list of paths for the obligations
     */
    public List<SymbexPath> visit(DafnyTree function) {

        assert function.getType() == DafnyParser.FUNCTION;

        LinkedList<SymbexPath> paths = new LinkedList<>();

        SymbexPath path = new SymbexPath(function);

        for (DafnyTree req : function.getChildrenWithType(DafnyParser.REQUIRES)) {
            path.addPathCondition(req.getLastChild(), req, AssumptionType.PRE);
        }

        //
        // Add assumption $mod = <readsclauses>
        DafnyTree reads = function.getChildrenWithType(DafnyParser.READS).stream().
                map(Util.runtimeException(ModifiesListResolver::resolve)).
                reduce(ASTUtil::setUnion).orElse(ASTUtil.setExt(List.of()));
        DafnyTree equality = ASTUtil.equals(ASTUtil.id("$mod"), reads);
        path.addPathCondition(equality, reads, AssumptionType.PRE);

        SymbexExpressionValidator validator = new SymbexExpressionValidator(paths, path, true);
        validator.handleExpression(function.getLastChild());

        return paths;
    }
}
