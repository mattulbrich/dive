/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.rules;

import edu.kit.iti.algover.script.ScriptTree;
import edu.kit.iti.algover.term.Sequent;
import nonnull.NonNull;
import nonnull.Nullable;

/**
 * Interface for Proof steps
 * Proof steps can be single rules, but also application of solvers etc.
 */
public interface ProofRule<P> {

    public @NonNull String getName();

    public ProofRuleApplication<P> consider(
            @NonNull P parameters,
            @NonNull Sequent sequent,
            @NonNull Sequent selection,
            @Nullable TermSelector selector) throws RuleException;

    public @NonNull P parseArguments(ScriptTree tree) throws RuleException;

}
