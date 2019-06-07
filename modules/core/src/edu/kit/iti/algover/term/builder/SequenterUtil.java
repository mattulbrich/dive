/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 *
 */

package edu.kit.iti.algover.term.builder;

import edu.kit.iti.algover.proof.ProofFormula;
import edu.kit.iti.algover.symbex.PathConditionElement;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.util.ImmutableList;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * A collection of static classes that have to do with turning symbolic
 * execution into sequents.
 *
 * In particular, it deals with adding labels.
 *
 * @author mattias ulbrich
 */
public class SequenterUtil {

    /**
     * The label to be used for path condition elements:
     * if- and while-guards (pos and neg)
     */
    public static final String PATH_COND_LABEL = "PathCond";

    /**
     * The label to be used for formulas representing the
     * symbolic execution path (with SSA mainly)
     */
    public static final String PATH_LABEL = "Path";

    /**
     * Assumptions (explicit or implicit)
     */
    public static final String ASSUMPTION_LABEL = "Assumption";

    /**
     * Preconditions (requires clauses)
     */
    public static final String PRE_COND_LABEL = "PreCond";

    /**
     * Things to show (usually at most one per sequent)
     */
    public static final String ASSERTION_LABEL = "Assertion";

    private SequenterUtil() {
        throw new Error();
    }

    /**
     * Get the label that should be attached to path condition elements based
     * on their type.
     *
     * @param pce the condition to evaluate
     * @return the String for the label to be displayed.
     */
    public static String getLabel(PathConditionElement pce) {
        switch (pce.getType()) {
        case IF_ELSE:
        case IF_THEN:
        case WHILE_FALSE:
        case WHILE_TRUE:
            return PATH_COND_LABEL;

        case ASSUMED_INVARIANT:
        case CALL_POST:
        case ASSUMED_ASSERTION:
        case EXPLICIT_ASSUMPTION:
        case IMPLICIT_ASSUMPTION:
        case GUARD_IN_EXPRESSION:
            return ASSUMPTION_LABEL;

        case PRE:
            return PRE_COND_LABEL;
        }

        return "Unknown";
    }


    public static List<ProofFormula> coalesceDuplicates(Iterable<ProofFormula> list) {
        Map<Term, ProofFormula> result = new LinkedHashMap<>();

        for (ProofFormula formula : list) {
            Term term = formula.getTerm();
            ProofFormula seen = result.get(term);
            if (seen == null) {
                result.put(term, formula);
            } else {
                ImmutableList<String> labels = seen.getLabels().
                        appendAll(formula.getLabels()).withoutDuplicates();
                result.put(term, new ProofFormula(term, labels));
            }
        }

        return new ArrayList<>(result.values());
    }
}
