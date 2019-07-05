/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 *
 */

package edu.kit.iti.algover.rules;

import edu.kit.iti.algover.rules.impl.AddHypothesisRule;
import edu.kit.iti.algover.rules.impl.ExhaustiveRule;
import edu.kit.iti.algover.rules.impl.NotLeftRule;
import edu.kit.iti.algover.term.Sort;

public class NotApplicableException extends RuleException {
    public NotApplicableException() {
    }

    public NotApplicableException(String message, Throwable cause, boolean enableSuppression, boolean writableStackTrace) {
        super(message, cause, enableSuppression, writableStackTrace);
    }

    public NotApplicableException(String message, Throwable cause) {
        super(message, cause);
    }

    public NotApplicableException(String message) {
        super(message);
    }

    public NotApplicableException(Throwable cause) {
        super(cause);
    }


    public static NotApplicableException onlyToplevel(ProofRule rule) throws NotApplicableException {
        return new NotApplicableException(rule.getName() + " can only be applied on toplevel formulas");
    }

    public static NotApplicableException onlySuccedent(ProofRule rule) {
        return new NotApplicableException(rule.getName() + " may only be applied on the succedent of a sequent");
    }

    public static NotApplicableException onlyAntecedent(ProofRule rule) {
        return new NotApplicableException(rule.getName() + " may only be applied on the antecedent of a sequent");
    }

    public static NotApplicableException onlyOperator(ProofRule rule, String op) {
        return new NotApplicableException(rule.getName() + " may only be applied to terms with operator '" + op + "'");
    }

    public static RuleException requiredSort(ProofRule rule, ParameterDescription<?> param, Sort expected, Sort actual) {
        return new NotApplicableException(rule.getName() + " expects a term of sort " + expected + " in parameter " +
                param.getName() + ", but received one of type " + actual);
    }

    public static NotApplicableException requiresParameter(ProofRule rule, ParameterDescription<?> param) {
        return new NotApplicableException(rule.getName() + " requires a parameter named '" + param.getName() + "' of type " +
                param.getType());
    }
}
