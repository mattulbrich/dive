/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.script.interpreter;

import edu.kit.iti.algover.script.ast.ASTNode;
import edu.kit.iti.algover.script.parser.Visitor;
import org.antlr.v4.runtime.ParserRuleContext;

import java.util.List;

/**
 * Handling of exntry and exit points in interpreter
 * @author Alexander Weigl
 * @version 1 (21.05.17)
 */
public interface ScopeObservable {
    /**
     * If new Block is entered, a new state has to be created
     * (copy of current state) and pushed to the stack
     */
    default  void enterScope(ASTNode node) {

        callListeners(getEntryListeners(), node);
    }

    /**
     * If block is extied the top state on the
     * stack has to be removed
     */
    default  void exitScope(ASTNode node) {
        callListeners(getExitListeners(), node);
    }

    List<Visitor<?>> getExitListeners();

    List<Visitor<?>> getEntryListeners();

    default  void callListeners(List<Visitor<?>> listeners, ASTNode node) {
        if (listeners.size() != 0) {
            listeners.forEach(node::accept);
        }
    }
}
