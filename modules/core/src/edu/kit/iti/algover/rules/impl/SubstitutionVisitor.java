/*
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.rules.impl;

import edu.kit.iti.algover.rules.RuleException;
import edu.kit.iti.algover.term.*;
import edu.kit.iti.algover.term.builder.TermBuildException;
import edu.kit.iti.algover.util.ImmutableList;
import edu.kit.iti.algover.util.Pair;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * Visitor for applying substitutions on Terms. Carefully handles shadowing of variables:
 * <code>let x := 5 :: let x, y := 6, x :: x</code> gets transformed into
 * <code>let x, y := 6, 5 :: x</code>.
 *
 * @author philipp
 *
 * @see edu.kit.iti.algover.term.builder.LetInlineVisitor
 */
public class SubstitutionVisitor implements TermVisitor<Map<String, Term>, Term, RuleException> {

    /**
     * store the bound variables encountered on the way.
     * Needed to detect conflicts.
     */
    private ImmutableList<VariableTerm> boundVars = ImmutableList.nil();

    /**
     * Variables get substituted, when they have something to be substituted in the
     * substitution table "substitutions".
     * TODO: unless they are being shadowed.
     */
    @Override
    public Term visit(VariableTerm variableTerm, Map<String, Term> substitutions) throws RuleException {
        String varname = variableTerm.getName();
        Term substitution = substitutions.get(varname);
        if (substitution == null) {
            return variableTerm;
        }

        Set<VariableTerm> freeVars = FreeVarVisitor.findFreeVars(substitution);
        if(boundVars.exists(freeVars::contains)) {
            // A substitution is conflicting if it introduces an occurrence into
            // the scope of a variable binder.
            throw new RuleException("Substitution induces a conflict: " + varname);
        }

        return substitution;
    }

    /**
     * SchemaVarTerms don't get changed.
     */
    @Override
    public Term visit(SchemaVarTerm schemaVarTerm, Map<String, Term> substitutions) {
        return schemaVarTerm;
    }

    /**
     * Quantifiers shadow via their bound variable. Inside of them substitutions mentioning the bound variable mustn't be
     * substituted.
     */
    @Override
    public Term visit(QuantTerm quantTerm, Map<String, Term> substitutions) throws RuleException {
        Term inner = quantTerm.getTerm(0);
        boundVars = boundVars.append(quantTerm.getBoundVar());
        Term innerReplaced = inner.accept(this,
                removeFromMap(substitutions, Collections.singleton(quantTerm.getBoundVar().getName())));
        boundVars = boundVars.getTail();
        if (innerReplaced == inner) { // We need to try to keep our term identity for the automatic reference generation
            return quantTerm; // return the previous pointer instead of generating a new QuantTerm with the same content (and losing the identity)
        } else {
            try {
                return new QuantTerm(quantTerm.getQuantifier(), quantTerm.getBoundVar(), innerReplaced);
            } catch (TermBuildException e) {
                e.printStackTrace();
                return quantTerm; // Hm I actually don't like this "recovering" strategy...
                // I don't expect this exception at all and want it to fail HARD when it happens
                // (philipp)
            }
        }
    }

    /**
     * Applications simply move on with the substitution recursively.
     */
    @Override
    public Term visit(ApplTerm applTerm, Map<String, Term> substitutions) throws RuleException {
        boolean anythingNew = false;
        Term[] subterms = new Term[applTerm.getSubterms().size()];
        for (int i = 0; i < applTerm.getSubterms().size(); i++) {
            Term inner = applTerm.getTerm(i);
            Term innerReplaced = inner.accept(this, substitutions);
            subterms[i] = innerReplaced;
            anythingNew |= !inner.equals(innerReplaced); // So that we know, when we cannot preserve identity anymore
        }
        if (!anythingNew) {
            // $heap() is a ApplTerm. Updates are handled by substitution. I. e., heap() is
            // substituted by Store(heap,...). If the heap is updated a substition of the for
            // "heap" -> .. is in the substitutions map.
            // So this is a quick fix (tests pass)
            if (subterms.length == 0) {
                Term sub = substitutions.get(applTerm.getSort().getName());
                if (sub != null)
                    return sub;
            }
            return applTerm;
        } else {
            try {
                return new ApplTerm(applTerm.getFunctionSymbol(), subterms);
            } catch (TermBuildException e) {
                e.printStackTrace();
                return applTerm; // see above.
            }
        }
    }

    /**
     * Let terms shadow with their bound variables for their inner term, but the expression that gets
     * bound to the variables still get all substitutions.
     */
    @Override
    public Term visit(LetTerm letTerm, Map<String, Term> substitutions) throws RuleException {
        // Substitute everything inside the let's definitions
        boolean substitutionsChanged = false;
        List<Pair<VariableTerm, Term>> substitutedLetSubstitutions = new ArrayList<>(letTerm.getSubstitutions().size());
        for (Pair<VariableTerm, Term> pair : letTerm.getSubstitutions()) {
            VariableTerm var = pair.fst;
            Term letSubst = pair.snd;
            // No need to shadow yet.
            Term letSubstChanged = letSubst.accept(this, substitutions);

            substitutedLetSubstitutions.add(new Pair<>(var, letSubstChanged));

            substitutionsChanged |= !letSubst.equals(letSubstChanged);
        }

        // Substitute the inner of the let
        ImmutableList<VariableTerm> oldBound = boundVars;
        List<String> letSubstitutions = new ArrayList<>();
        for (Pair<VariableTerm, Term> subst : letTerm.getSubstitutions()) {
            letSubstitutions.add(subst.fst.getName());
            boundVars = boundVars.append(subst.fst);
        }

        // The effect of shadowing variables from outer lets inside the inner ones
        Map<String, Term> trimmedSubstitutions = removeFromMap(substitutions, letSubstitutions);
        Term inner = letTerm.getTerm(0);
        Term innerReplaced = inner.accept(this, trimmedSubstitutions);

        boundVars = oldBound;

        if (inner == innerReplaced && !substitutionsChanged) { // preserve identity again, see above
            return letTerm;
        } else {
            try {
                return new LetTerm(substitutedLetSubstitutions, innerReplaced);
            } catch (TermBuildException e) {
                e.printStackTrace();
                return letTerm;
            }
        }
    }

    private Map<String, Term> removeFromMap(Map<String, Term> map, Iterable<String> keys) {
        boolean containsAnyKey = false;
        for (String key : keys) {
            containsAnyKey |= map.containsKey(key);
        }
        if (!containsAnyKey) {
            return map;
        }
        Map<String, Term> shallowCopied = new HashMap<>(map);
        for (String key : keys) {
            shallowCopied.remove(key);
        }
        return shallowCopied;
    }
}

//    /*
//     * If the variable is in the substitution map then return the substitution.
//     * Return null (unchanged) otherwise.
//     */
//    @Override
//    public Term visit(VariableTerm variableTerm, Map<String, Term> map) throws TermBuildException {
//        return map.get(variableTerm.getName());
//    }
//
//    @Override
//    public Term visit(LetTerm letTerm, Map<String, Term> arg) throws TermBuildException {
//        // The visitor needs a copy of the map as it may temporarily modified
//        return super.visit(letTerm, new HashMap<>(arg));
//    }
//
//    @Override
//    public VariableTerm visitLetTarget(VariableTerm variableTerm, Map<String, Term> arg) throws TermBuildException {
//        return visitBoundVariable(variableTerm, arg);
//    }
//
//    @Override
//    public Term visit(QuantTerm quantTerm, Map<String, Term> arg) throws TermBuildException {
//        // The visitor needs a copy of the map as it may temporarily modified
//        return super.visit(quantTerm, new HashMap<>(arg));
//    }
//
//    @Override
//    public VariableTerm visitBoundVariable(VariableTerm variableTerm, Map<String, Term> arg) throws TermBuildException {
//
//        arg.remove(variableTerm.getName());
//
//        Set<String> freeVarsName = FreeVarVisitor.findFreeVars(arg.values()).stream().
//                map(VariableTerm::getName).collect(Collectors.toSet());
//
//        if (!freeVarsName.contains(variableTerm.getName())) {
//            return null;
//        }
//
//        VariableTerm newVarTerm = variableTerm;
//        int variant = 1;
//        do {
//            newVarTerm = new VariableTerm(variableTerm.getName() + "_" + variant,
//                    variableTerm.getSort());
//            variant ++;
//        } while (freeVarsName.contains(newVarTerm.getName()));
//
//        arg.put(variableTerm.getName(), newVarTerm);
//
//        return newVarTerm;
//    }