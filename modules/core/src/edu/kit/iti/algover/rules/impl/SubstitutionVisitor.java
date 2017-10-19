package edu.kit.iti.algover.rules.impl;

import de.uka.ilkd.pp.NoExceptions;
import edu.kit.iti.algover.script.ast.Variable;
import edu.kit.iti.algover.term.*;
import edu.kit.iti.algover.term.builder.TermBuildException;
import edu.kit.iti.algover.util.Pair;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

public class SubstitutionVisitor implements TermVisitor<Map<String, Term>, Term, NoExceptions> {
    @Override
    public Term visit(VariableTerm variableTerm, Map<String, Term> substitutions) throws NoExceptions {
        String varname = variableTerm.getName();
        Term substitution = substitutions.get(varname);
        return substitution == null ? variableTerm : substitution;
    }

    @Override
    public Term visit(SchemaVarTerm schemaVarTerm, Map<String, Term> substitutions) throws NoExceptions {
        return schemaVarTerm;
    }

    @Override
    public Term visit(QuantTerm quantTerm, Map<String, Term> substitutions) throws NoExceptions {
        Term inner = quantTerm.getTerm(0);
        Term innerReplaced = inner.accept(this, removeFromMap(substitutions, quantTerm.getBoundVar().getName()));
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

    @Override
    public Term visit(ApplTerm applTerm, Map<String, Term> substitutions) throws NoExceptions {
        boolean anythingNew = false;
        Term[] subterms = new Term[applTerm.getSubterms().size()];
        for (int i = 0; i < applTerm.getSubterms().size(); i++) {
            Term inner = applTerm.getTerm(i);
            Term innerReplaced = inner.accept(this, substitutions);
            subterms[i] = innerReplaced;

            anythingNew |= inner != innerReplaced; // So that we know, when we cannot preserve identity anymore
        }
        if (!anythingNew) {
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

    @Override
    public Term visit(LetTerm letTerm, Map<String, Term> substitutions) throws NoExceptions {
        // Substitute everything inside the let's definitions
        boolean substitutionsChanged = false;
        List<Pair<VariableTerm, Term>> substitutedLetSubstitutions = new ArrayList<>(letTerm.getSubstitutions().size());
        for (Pair<VariableTerm, Term> pair : letTerm.getSubstitutions()) {
            VariableTerm var = pair.fst;
            Term letSubst = pair.snd;
            Term letSubstChanged = letSubst.accept(this, substitutions); // No need to shadow yet
            substitutedLetSubstitutions.add(new Pair<>(var, letSubstChanged));

            substitutionsChanged |= letSubst != letSubstChanged;
        }

        // Substitute the inner of the let
        String[] letSubstitutions = letTerm.getSubstitutions().stream()
                .map(Pair::getFst)
                .map(VariableTerm::getName)
                .collect(Collectors.toList())
                .toArray(new String[0]);
        // The effect of shadowing variables from outer lets inside the inner ones
        Map<String, Term> trimmedSubstitutions = removeFromMap(substitutions, letSubstitutions);
        Term inner = letTerm.getTerm(0);
        Term innerReplaced = inner.accept(this, trimmedSubstitutions);

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

    private Map<String, Term> removeFromMap(Map<String, Term> map, String... keys) {
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
