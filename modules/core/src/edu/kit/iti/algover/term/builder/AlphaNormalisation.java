/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.term.builder;

import de.uka.ilkd.pp.NoExceptions;
import edu.kit.iti.algover.script.ast.Variable;
import edu.kit.iti.algover.term.ApplTerm;
import edu.kit.iti.algover.term.DefaultTermVisitor;
import edu.kit.iti.algover.term.LetTerm;
import edu.kit.iti.algover.term.QuantTerm;
import edu.kit.iti.algover.term.SchemaCaptureTerm;
import edu.kit.iti.algover.term.SchemaOccurTerm;
import edu.kit.iti.algover.term.SchemaTerm;
import edu.kit.iti.algover.term.SchemaVarTerm;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.term.TermVisitor;
import edu.kit.iti.algover.term.VariableTerm;
import edu.kit.iti.algover.util.ImmutableLinearMap;
import edu.kit.iti.algover.util.ImmutableMap;
import edu.kit.iti.algover.util.ImmutableSet;
import edu.kit.iti.algover.util.Immutables;
import edu.kit.iti.algover.util.Pair;
import edu.kit.iti.algover.util.Util;
import nonnull.NonNull;

import java.util.ArrayList;
import java.util.List;
import java.util.Objects;

/**
 * The methods in this class can be used to make sure that a term has no
 * name clashes.
 *
 * A bound variable must not hide a used constant. In "let x := 3 :: x==x",
 * it must not be that the last x is not the variable, but a constant
 * (coincidently named x).
 *
 * One important consequence of the normalisation process is that
 * normalised terms are meant to have the property that
 * <code>
 *     TermParser.parse(symbols, term.toString()).equals(term)
 * </code>
 * is true for all (non-null) terms if the symbol table is complete.
 *
 * In the past there were a few incidences with non-normalised formulas
 * on the sequent.
 *
 * It is therefore checked by an assertion that any ProofFormula contains a
 * normalised formula.
 *
 * If required at some point., the {@link #normalise(Term)} method can be
 * implemented which renames variables to ensure normalised terms.
 *
 * @author mattias ulbrich
 */
public class AlphaNormalisation {

    public static @NonNull Term normalise(@NonNull Term term) throws TermBuildException {
        NameClashHandler nd = new NameClashHandler(false);
        return term.accept(nd, Immutables.emptyMap());
    }

    public static boolean isNormalised(@NonNull Term term) {
        NameClashHandler nd = new NameClashHandler(true);
        try {
            term.accept(nd, Immutables.emptyMap());
            return true;
        } catch (TermBuildException e) {
            return false;
        }
    }

    public static void assertNormalised(@NonNull Term term) {
        if(AlphaNormalisation.class.desiredAssertionStatus()) {
            NameClashHandler nd = new NameClashHandler(true);
            try {
                term.accept(nd, Immutables.emptyMap());
            } catch (TermBuildException e) {
                throw new AssertionError("Term not normalised: " + term, e);
            }
        }
    }

    private static class VariableViolation extends TermBuildException {
        private final VariableTerm var;

        public VariableViolation(VariableTerm var) {
            super("Violation: " + var);
            this.var = var;
        }

        public VariableTerm getVar() {
            return var;
        }
    }

    private static class UnboundNameDetector implements
            TermVisitor<Void, ImmutableSet<Term>, NoExceptions> {

        @Override
        public ImmutableSet<Term> visit(VariableTerm variableTerm, Void arg) throws NoExceptions {
            return Immutables.setOf(variableTerm);
        }

        @Override
        public ImmutableSet<Term> visit(QuantTerm quantTerm, Void arg) throws NoExceptions {
            ImmutableSet<Term> matrixNames = quantTerm.getTerm(0).accept(this, null);
            return matrixNames.remove(quantTerm.getBoundVar());
        }

        @Override
        public ImmutableSet<Term> visit(ApplTerm applTerm, Void arg) throws NoExceptions {
            if (applTerm.countTerms() == 0) {
                return Immutables.setOf(applTerm);
            } else {
                ImmutableSet<Term> result = Immutables.emptySet();
                for (Term subterm : applTerm.getSubterms()) {
                    result = result.addAll(subterm.accept(this, null));
                }
                return result;
            }
        }

        @Override
        public ImmutableSet<Term> visit(LetTerm letTerm, Void arg) throws NoExceptions {

            ImmutableSet<Term> result = Immutables.emptySet();
            for (Pair<VariableTerm, Term> subst : letTerm.getSubstitutions()) {
                result = result.addAll(subst.snd.accept(this, null));
            }

            ImmutableSet<Term> matrixResult = letTerm.getTerm(0).accept(this, null);
            matrixResult = matrixResult.removeAll(Util.map(letTerm.getSubstitutions(), Pair::getFst));

            result = result.addAll(matrixResult);

            return result;
        }

        @Override
        public ImmutableSet<Term> visitSchemaTerm(SchemaTerm schemaTerm, Void arg) throws NoExceptions {
            ImmutableSet<Term> result = Immutables.emptySet();
            for (Term subterm : schemaTerm.getSubterms()) {
                result = result.addAll(subterm.accept(this, null));
            }
            return result;
        }
    }

    private static class NameClashHandler extends ReplacementVisitor<ImmutableMap<VariableTerm, VariableTerm>> {

        private final boolean detectOnly;
        private final UnboundNameDetector detector = new UnboundNameDetector();

        private NameClashHandler(boolean detectOnly) {
            this.detectOnly = detectOnly;
        }

        @Override
        public Term visit(VariableTerm term, ImmutableMap<VariableTerm, VariableTerm> replacements) {
            return replacements.get(term);
        }

        @Override
        public Term visit(QuantTerm quantTerm, ImmutableMap<VariableTerm, VariableTerm> replacements) throws TermBuildException {
            VariableTerm boundVar = quantTerm.getBoundVar();
            ImmutableSet<Term> unbounds = quantTerm.getTerm(0).accept(detector, null);
            unbounds = unbounds.remove(boundVar);
            VariableTerm newBoundVar = mkNewVar(boundVar, unbounds);
            if (newBoundVar == boundVar) {
                return super.visit(quantTerm, replacements);
            } else {
                // There is a name clash!
                Term matrix = quantTerm.getTerm(0).accept(this, replacements.put(boundVar, newBoundVar));
                return new QuantTerm(quantTerm.getQuantifier(), newBoundVar, matrix);
            }
        }

        @Override
        public Term visit(LetTerm letTerm, ImmutableMap<VariableTerm, VariableTerm> arg) throws TermBuildException {
            ImmutableSet<Term> unbounds = letTerm.getTerm(0).accept(detector, null);
            unbounds = unbounds.removeAll(Util.map(letTerm.getSubstitutions(), Pair::getFst));
            unbounds = unbounds.map(v -> v instanceof VariableTerm ?
                    arg.getOrDefault((VariableTerm)v, (VariableTerm)v) : v);

            List<Pair<VariableTerm, Term>> newSubsts = new ArrayList<>();
            ImmutableMap<VariableTerm, VariableTerm> innerReplacements = arg;
            boolean changed = false;
            for (Pair<VariableTerm, Term> subst : letTerm.getSubstitutions()) {
                VariableTerm newVar = mkNewVar(subst.getFst(), unbounds);
                if (newVar != subst.fst) {
                    changed = true;
                    innerReplacements = innerReplacements.put(subst.fst, newVar);
                }

                Term newAssignment = subst.snd.accept(this, arg);
                if (newAssignment == null) {
                    newAssignment = subst.snd;
                } else {
                    changed = true;
                }

                newSubsts.add(new Pair<>(newVar, newAssignment));
            }

            Term matrix = letTerm.getTerm(0).accept(this, innerReplacements);
            if (matrix == null) {
                matrix = letTerm.getTerm(0);
            } else {
                changed = true;
            }

            if (changed) {
                return new LetTerm(newSubsts, matrix);
            } else {
                return null;
            }
        }

        @Override
        public Term visit(SchemaVarTerm schemaVarTerm, ImmutableMap<VariableTerm, VariableTerm> arg) throws TermBuildException {
            return null;
        }

        @Override
        public Term visit(SchemaOccurTerm occurTerm, ImmutableMap<VariableTerm, VariableTerm> arg) throws TermBuildException {
            Term inner = occurTerm.getTerm(0).accept(this, arg);
            if (inner == null) {
                return null;
            } else {
                return new SchemaOccurTerm(inner);
            }
        }

        @Override
        public Term visit(SchemaCaptureTerm captureTerm, ImmutableMap<VariableTerm, VariableTerm> arg) throws TermBuildException {
            Term inner = captureTerm.getTerm(0).accept(this, arg);
            if (inner == null) {
                return null;
            } else {
                return new SchemaCaptureTerm(captureTerm.getName(), inner);
            }
        }

        private VariableTerm mkNewVar(VariableTerm var, ImmutableSet<Term> unboundedTerms) throws VariableViolation {

            ImmutableSet<String> names = unboundedTerms.map(Objects::toString);
            String orgName = var.getName();
            if (names.contains(orgName)) {
                if (detectOnly) {
                    throw new VariableViolation(var);
                }
               int index = 1;
               String name = orgName + "_" + index;
               while(names.contains(name)) {
                   index++;
                   name = orgName + "_" + index;
               }
                return new VariableTerm(name, var.getSort());
            } else {
                // there is no clash ...
                return var;
            }

        }
    }
}
