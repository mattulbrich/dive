package edu.kit.iti.algover.script.parser;

/*-
 * #%L
 * ProofScriptParser
 * %%
 * Copyright (C) 2017 Application-oriented Formal Verification
 * %%
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as
 * published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 * 
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 * 
 * You should have received a copy of the GNU General Public
 * License along with this program.  If not, see
 * <http://www.gnu.org/licenses/gpl-3.0.html>.
 * #L%
 */


import edu.kit.iti.algover.script.ast.*;

import java.util.ArrayList;
import java.util.Map;
import java.util.Set;

/**
 * {@link ASTChanger} provides a visitor with for replacing or substiting nodes (in situ).
 *
 * @author Alexander Weigl
 * @version 1 (29.04.17)
 */
public class ASTChanger extends DefaultASTVisitor<ASTNode> {
    @Override
    public ProofScript visit(ProofScript proofScript) {
        proofScript.setBody((Statements) proofScript.getBody().accept(this));
        return proofScript;
    }

    @Override
    public AssignmentStatement visit(AssignmentStatement assign) {
        assign.setRhs((Expression) assign.getRhs().accept(this));
        assign.setLhs((Variable) assign.getLhs().accept(this));
        return assign;
    }

    @Override
    public Expression visit(BinaryExpression e) {
        e.setLeft((Expression) e.getLeft().accept(this));
        e.setRight((Expression) e.getRight().accept(this));
        return e;
    }

    @Override
    public MatchExpression visit(MatchExpression match) {
        if (match.getSignature() != null)
            match.setSignature((Signature)
                    match.getSignature().accept(this));

        match.setPattern((Expression) match.getPattern().accept(this));
        return match;
    }

    @Override
    public TermLiteral visit(TermLiteral term) {
        return term;
    }

    @Override
    public StringLiteral visit(StringLiteral string) {
        return string;
    }

    @Override
    public Variable visit(Variable variable) {
        return variable;
    }

    @Override
    public BooleanLiteral visit(BooleanLiteral bool) {
        return bool;
    }

    @Override
    public Statements visit(Statements statements) {
        ArrayList copy = new ArrayList<>(statements.size());
        for (Statement statement : statements) {
            copy.add(statement.accept(this));
        }
        statements.clear();
        statements.addAll(copy);
        return statements;
    }

    @Override
    public IntegerLiteral visit(IntegerLiteral integer) {
        return integer;
    }

    @Override
    public CasesStatement visit(CasesStatement casesStatement) {
        for (CaseStatement c : casesStatement.getCases()) {
            c.accept(this);
        }
        return casesStatement;
    }

    @Override
    public IsClosableCase visit(IsClosableCase isClosableCase) {
        isClosableCase.getBody().accept(this);
        return isClosableCase;
    }

    @Override
    public SimpleCaseStatement visit(SimpleCaseStatement simpleCaseStatement) {
        simpleCaseStatement.getGuard().accept(this);
        simpleCaseStatement.getBody().accept(this);
        return simpleCaseStatement;
    }

    @Override
    public CaseStatement visit(CaseStatement caseStatement) {
        //caseStatement.getGuard().accept(this);
        //caseStatement.getBody().accept(this);
        caseStatement.accept(this);
        return caseStatement;

    }

    @Override
    public CallStatement visit(CallStatement call) {
        call.setParameters((Parameters) call.getParameters().accept(this));
        return call;
    }
/*
    @Override
    public ASTNode visit(TheOnlyStatement theOnly) {
        theOnly.setBody((Statements) theOnly.getBody().accept(this));
        return theOnly;
    }

    @Override
    public ASTNode visit(ForeachStatement foreach) {
        foreach.setBody((Statements) foreach.getBody().accept(this));
        return foreach;
    }

    @Override
    public ASTNode visit(RepeatStatement repeat) {
        repeat.setBody((Statements) repeat.getBody().accept(this));
        return repeat;
    }*/

    @Override
    public ASTNode visit(Signature signature) {
        Set<Map.Entry<Variable, Type>> entries = signature.entrySet();
        signature.clear();
        for (Map.Entry<Variable, Type> e : entries) {
            signature.put((Variable) e.getKey().accept(this), e.getValue());
        }
        return signature;
    }

    @Override
    public ASTNode visit(Parameters parameters) {
        Set<Map.Entry<Variable, Expression>> entries = parameters.entrySet();
        parameters.clear();
        for (Map.Entry<Variable, Expression> e : entries) {
            parameters.put((Variable) e.getKey().accept(this), e.getValue());
        }
        return parameters;
    }

    @Override
    public ASTNode visit(UnaryExpression e) {
        e.setExpression((Expression) e.getExpression().accept(this));
        return e;
    }
}
