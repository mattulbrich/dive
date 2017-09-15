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

/**
 * @author Alexander Weigl
 * @version 1 (27.04.17)
 */
public interface Visitor<T> {
    T visit(ProofScript proofScript);

    T visit(AssignmentStatement assign);

    T visit(BinaryExpression e);

    T visit(MatchExpression match);

    T visit(TermLiteral term);

    T visit(SequentLiteral sequentLiteral);

    T visit(StringLiteral string);

    T visit(Variable variable);

    T visit(BooleanLiteral bool);

    T visit(Statements statements);

    T visit(IntegerLiteral integer);

    T visit(CasesStatement cases);

    //T visit(CaseStatement case_);

    T visit(CallStatement call);

    /*
        T visit(TheOnlyStatement theOnly);

        T visit(ForeachStatement foreach);

        T visit(RepeatStatement repeat);
    */
    T visit(Signature signature);

    T visit(Parameters parameters);

    T visit(UnaryExpression e);


    T visit(IsClosableCase isClosableCase);

    T visit(SimpleCaseStatement simpleCaseStatement);

    T visit(CaseStatement caseStatement);
}
