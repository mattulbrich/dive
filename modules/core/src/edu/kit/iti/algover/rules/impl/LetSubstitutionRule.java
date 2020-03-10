/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.rules.impl;

import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.rules.*;
import edu.kit.iti.algover.term.LetTerm;
import edu.kit.iti.algover.term.Sequent;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.term.match.Matching;
import edu.kit.iti.algover.term.match.SequentMatcher;
import edu.kit.iti.algover.util.ImmutableList;
import edu.kit.iti.algover.util.RuleUtil;

import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

/**
 * A built-in rule that can be applied to let-terms inline all their bound variables via substitution.
 * <p>
 * (see {@link SubstitutionVisitor} for an example.)
 *
 * @author philipp
 */
public class LetSubstitutionRule extends FocusProofRule {

    @Override
    public String getName() {
        return "substitute";
    }

    @Override
    public String getCategory() {
        return ProofRuleCategories.SIMPLIFICATIONS;
    }

    @Override
    public ProofRuleApplication makeApplicationImpl(ProofNode target, Parameters parameters) throws RuleException {
        TermParameter onParam = parameters.getValue(ON_PARAM_REQ);
        Term on = onParam.getTerm();

        if (!(on instanceof LetTerm)) {
            throw NotApplicableException.onlyOperator(this, "let");
        }

        LetTerm targetLet = (LetTerm) on;

        TermSelector selector = onParam.getTermSelector();

        ProofRuleApplicationBuilder builder = new ProofRuleApplicationBuilder(this);

        builder.setApplicability(ProofRuleApplication.Applicability.APPLICABLE);
        builder.newBranch().addReplacement(selector, applyLetSubstitution(targetLet));

        return builder.build();
    }

    private static Term applyLetSubstitution(LetTerm targetLet) throws RuleException {
        Map<String, Term> substitutionMap =
                targetLet.getSubstitutions()
                        .stream()
                        .collect(Collectors.toMap(pair -> pair.fst.getName(), pair -> pair.snd));

        Term inner = targetLet.getTerm(0);
        return inner.accept(new SubstitutionVisitor(), substitutionMap);
    }
}
