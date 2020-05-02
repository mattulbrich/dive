/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.term.builder;

import edu.kit.iti.algover.parser.DafnyTree;
import edu.kit.iti.algover.proof.ProofFormula;
import edu.kit.iti.algover.term.LetTerm;
import edu.kit.iti.algover.term.QuantTerm;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.term.VariableTerm;
import edu.kit.iti.algover.util.Pair;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

public class ParallelUpdateSequenter extends UpdateSequenter {

    @Override
    public String getName() {
        return "ass-parallel";
    }

    @Override
    public String getDescriptiveName() {
        return "Parallel assignments in front of every formula";
    }

    @Override
    protected ProofFormula postProcess(ProofFormula formula, Map<Term, DafnyTree> referenceMap) throws TermBuildException {
        Map<VariableTerm, Term> substitution = new LinkedHashMap<>();

        Term term = formula.getTerm();
        while(term instanceof LetTerm) {
            LetTerm letTerm = (LetTerm) term;
            updateSubstitution(substitution,letTerm.getSubstitutions());
            term = letTerm.getTerm(0);
        }

        List<Pair<VariableTerm, Term>> newAssignments = new ArrayList<>();
        substitution.forEach((v, t) -> newAssignments.add(new Pair<>(v, t)));

        Term resultTerm;
        if(newAssignments.isEmpty()) {
            resultTerm = term;
        } else {
            resultTerm = new LetTerm(newAssignments, term);
        }

        return new ProofFormula(resultTerm, formula.getLabels());
    }

    private void updateSubstitution(Map<VariableTerm, Term> substitution, List<Pair<VariableTerm, Term>> assignments) throws TermBuildException {
        Map<VariableTerm, Term> update = new LinkedHashMap<>();
        for (Pair<VariableTerm, Term> entry : assignments) {
            Term instantiated = entry.snd.accept(InstantiationVisitor.INSTANCE, substitution);
            if (instantiated == null) {
                // will be null if it is not substituted.
                instantiated = entry.snd;
            }
            update.put(entry.fst, instantiated);
        }
        substitution.putAll(update);
    }
}

/**
 * This little class applies the substitution it receives as argument to the
 * term it walks over.
 */
class InstantiationVisitor extends ReplacementVisitor<Map<VariableTerm, Term>> {
    public static final InstantiationVisitor INSTANCE = new InstantiationVisitor();

    @Override
    public Term visit(VariableTerm variableTerm, Map<VariableTerm, Term> substitution) throws TermBuildException {
        return substitution.get(variableTerm);
    }

    /*
     * Do not update variables under the let binder
     * // see testConflictSmall* in test cases why this is needed.
     */
    @Override
    public Term visit(LetTerm letTerm, Map<VariableTerm, Term> arg) throws TermBuildException {
        LinkedHashMap<VariableTerm, Term> newMap = new LinkedHashMap<>(arg);
        letTerm.getSubstitutions().forEach(pair -> newMap.remove(pair.fst));

        return super.visit(letTerm, newMap);
    }

    /*
     * Do not update variables under the let binder
     * // see testConflictSmall* in test cases why this is needed.
     */
    @Override
    public Term visit(QuantTerm quantTerm, Map<VariableTerm, Term> arg) throws TermBuildException {
        LinkedHashMap<VariableTerm, Term> newMap = new LinkedHashMap<>(arg);
        newMap.remove(quantTerm.getBoundVar());

        return super.visit(quantTerm, newMap);
    }
}