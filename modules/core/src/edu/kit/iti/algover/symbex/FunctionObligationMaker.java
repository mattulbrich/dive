/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.symbex;

import edu.kit.iti.algover.parser.DafnyParser;
import edu.kit.iti.algover.parser.DafnyTree;
import edu.kit.iti.algover.symbex.PathConditionElement.AssumptionType;

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

    public List<SymbexPath> visit(DafnyTree function) {

        assert function.getType() == DafnyParser.FUNCTION;

        LinkedList<SymbexPath> paths = new LinkedList<>();

        SymbexPath path = new SymbexPath(function);

        for (DafnyTree req : function.getChildrenWithType(DafnyParser.REQUIRES)) {
            path.addPathCondition(req.getLastChild(), req, AssumptionType.PRE);
        }

        SymbexExpressionValidator.handleExpression(paths, path, function.getLastChild());

        return paths;
    }
}
