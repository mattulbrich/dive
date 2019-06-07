/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.script.parser;

/*-
 * #%L
 * ProofScriptParser
 * %%
 * Copyright (C) 2017 Application-oriented Formal Verification
 * %%
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General default License as
 * published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 * 
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General default License for more details.
 * 
 * You should have received a copy of the GNU General default
 * License along with this program.  If not, see
 * <http://www.gnu.org/licenses/gpl-3.0.html>.
 * #L%
 */


import edu.kit.iti.algover.script.ast.*;

import java.util.Map;

/**
 * {@link ASTTraversal} provides a visitor with a a default traversal of the given AST.
 *
 * @author Alexander Weigl
 * @version 1 (29.04.17)
 */

// REVIEW: Add the missing generic parameters! Please!

@SuppressWarnings({"unchecked", "rawtypes"})
public interface ASTTraversal<T> extends Visitor<T> {
    @Override
    default T visit(ProofScript proofScript) {
        proofScript.getSignature().accept(this);
        proofScript.getBody().accept(this);
        return null;
    }

    @Override
    default T visit(AssignmentStatement assign) {
        assign.getLhs().accept(this);
        return null;
    }

    @Override
    default T visit(BinaryExpression e) {
        e.getLeft().accept(this);
        e.getRight().accept(this);
        return null;
    }

    @Override
    default T visit(MatchExpression match) {
        match.getPattern().accept(this);
        match.getSignature().accept(this);
        return null;
    }

    @Override
    default T visit(TermLiteral term) {
        return null;
    }

    @Override
    default T visit(StringLiteral string) {
        return null;
    }

    @Override
    default T visit(Variable variable) {
        return null;
    }

    @Override
    default T visit(BooleanLiteral bool) {
        return null;
    }

    @Override
    default T visit(Statements statements) {
        for (Statement statement : statements) {
            statement.accept(this);
        }
        return null;
    }

    @Override
    default T visit(IntegerLiteral integer) {
        return null;
    }

    @Override
    default T visit(CasesStatement casesStatement) {
        for (CaseStatement c : casesStatement.getCases()) {
            c.accept(this);
        }
        return null;
    }

    @Override
    default T visit(CaseStatement caseStatement) {
        //caseStatement.getBody().accept(this);
        caseStatement.accept(this);
        return null;
    }

    @Override
    default T visit(CallStatement call) {
        for (Expression e : call.getParameters().values()) {
            e.accept(this);
        }
        return null;
    }

    /*@Override
    default T visit(TheOnlyStatement theOnly) {
        theOnly.getBody().accept(this);
        return null;
    }

    @Override
    default T visit(ForeachStatement foreach) {
        foreach.getBody().accept(this);
        return null;
    }

    @Override
    default T visit(RepeatStatement repeatStatement) {
        repeatStatement.getBody().accept(this);
        return null;
    }*/

    @Override
    default T visit(Signature signature) {
        for (Map.Entry<Variable, Type> e : signature.entrySet()) {
            e.getKey().accept(this);
        }
        return null;
    }

    @Override
    // REVIEW: Repair when others are repaired
    @SuppressWarnings({"rawtypes"})
    default T visit(Parameters parameters) {
        for (Map.Entry<Variable, Expression> e :
                parameters.entrySet()) {
            e.getKey().accept(this);
            e.getValue().accept(this);
        }
        return null;
    }

    @Override
    default T visit(UnaryExpression e) {
        e.getExpression().accept(this);
        return null;
    }

    @Override
    default T visit(IsClosableCase isClosableCase) {
        isClosableCase.getBody().accept(this);
        return null;
    }

    @Override
    default T visit(SimpleCaseStatement simpleCaseStatement) {
        simpleCaseStatement.getGuard().accept(this);
        simpleCaseStatement.getBody().accept(this);
        return null;
    }
}
