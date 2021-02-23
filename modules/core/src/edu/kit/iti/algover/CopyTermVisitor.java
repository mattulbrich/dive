/*
 * This file is part of DIVE.
 *
 * DIVE is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * Foobar is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with Foobar.  If not, see <https://www.gnu.org/licenses/>.
 */

package edu.kit.iti.algover;

import edu.kit.iti.algover.term.*;
import edu.kit.iti.algover.term.builder.TermBuildException;
import edu.kit.iti.algover.util.Pair;

import java.util.ArrayList;
import java.util.List;

/**
 * Visitor which creates an identical Copy of the provided term
 */
public class CopyTermVisitor implements TermVisitor<Void, Term, TermBuildException> {
    public Term visit(Term t) throws TermBuildException {
        if(t instanceof VariableTerm) {
            return visit((VariableTerm) t, null);
        }
        if(t instanceof QuantTerm) {
            return visit((QuantTerm) t, null);
        }
        if(t instanceof ApplTerm) {
            return visit((ApplTerm) t, null);
        }
        if(t instanceof LetTerm) {
            return visit((LetTerm) t, null);
        }
        if(t instanceof SchemaVarTerm) {
            return visit((SchemaVarTerm) t, null);
        }
        if(t instanceof SchemaOccurTerm) {
            return visit((SchemaOccurTerm) t, null);
        }
        if(t instanceof SchemaEllipsisTerm) {
            return visit((SchemaEllipsisTerm) t, null);
        }
        if(t instanceof SchemaCaptureTerm) {
            return visit((SchemaCaptureTerm) t, null);
        }
        throw new TermBuildException("Visited unknown Term-type.");
    }

    @Override
    public Term visit(VariableTerm variableTerm, Void arg) throws TermBuildException {
        return new VariableTerm(variableTerm.getName(), variableTerm.getSort());
    }

    @Override
    public Term visit(QuantTerm quantTerm, Void arg) throws TermBuildException {
        return new QuantTerm(quantTerm.getQuantifier(), (VariableTerm)visit(quantTerm.getBoundVar()), new SchemaEllipsisTerm());
    }

    @Override
    public Term visit(ApplTerm applTerm, Void arg) throws TermBuildException {
        List<Term> arguments = new ArrayList<>();
        for(Term t : applTerm.getSubterms()) {
            arguments.add(visit(t));
        }
        return new ApplTerm(applTerm.getFunctionSymbol(), arguments);
    }

    @Override
    public Term visit(SchemaOccurTerm occurTerm, Void arg) throws TermBuildException {
        return new SchemaOccurTerm(new SchemaEllipsisTerm(), occurTerm.getSort());
    }

    @Override
    public Term visit(SchemaVarTerm schemaVarTerm, Void arg) throws TermBuildException {
        return new SchemaVarTerm(schemaVarTerm.getName(), schemaVarTerm.getSort());
    }

    @Override
    public Term visit(SchemaCaptureTerm schemaCaptureTerm, Void arg) throws TermBuildException {
        return new SchemaCaptureTerm(schemaCaptureTerm.getName(), new SchemaEllipsisTerm());
    }

    @Override
    public Term visitSchemaTerm(SchemaTerm schemaTerm, Void arg) throws TermBuildException {
        return visit(schemaTerm);
    }

    @Override
    public Term visit(LetTerm letTerm, Void arg) throws TermBuildException {
        List<Pair<VariableTerm, Term>> subs = new ArrayList<>();
        for(Pair<VariableTerm, Term> p : letTerm.getSubstitutions()) {
            subs.add(new Pair<VariableTerm, Term>((VariableTerm) visit(p.fst), visit(p.snd)));
        }
        return new LetTerm(subs, new SchemaEllipsisTerm());
    }
}
