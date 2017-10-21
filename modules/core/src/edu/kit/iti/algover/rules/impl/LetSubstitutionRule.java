package edu.kit.iti.algover.rules.impl;

import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.rules.*;
import edu.kit.iti.algover.term.LetTerm;
import edu.kit.iti.algover.term.Sequent;
import edu.kit.iti.algover.term.Term;

import java.util.Collections;
import java.util.HashMap;
import java.util.Map;
import java.util.stream.Collectors;

/**
 * A built-in rule that can be applied to let-terms inline all their bound variables via substitution.
 *
 * (see {@link SubstitutionVisitor} for an example.)
 *
 * @author philipp
 */
public class LetSubstitutionRule extends AbstractProofRule {

    private static Map<String, Class<?>> makeRequiredParameters() {
        Map<String, Class<?>> params = new HashMap<>();
        params.put("on", Term.class);
        return params;
    }

    /**
     * Builds a new SubstitutionRule.
     *
     * This rule only requires the "on" parameter, the term that it should be applied on.
     * That term <strong>must</strong> be a let term.
     */
    public LetSubstitutionRule() {
        super(makeRequiredParameters(), Collections.emptyMap());
    }

    @Override
    public String getName() {
        return "substitute";
    }

    @Override
    public ProofRuleApplication considerApplication(ProofNode target, Sequent selection, TermSelector selector) throws RuleException {
        Term targetTerm = selector.selectSubterm(selection);
        if (!(targetTerm instanceof LetTerm)) {
            return ProofRuleApplicationBuilder.notApplicable(this);
        }
        LetTerm targetLet = (LetTerm) targetTerm;

        Map<String, Term> substitutionMap =
                targetLet.getSubstitutions()
                        .stream()
                        .collect(Collectors.toMap(pair -> pair.fst.getName(), pair -> pair.snd));

        Term inner = targetLet.getTerm(0);
        Term innerWithSubstitutions = inner.accept(new SubstitutionVisitor(), substitutionMap);

        ProofRuleApplicationBuilder builder = new ProofRuleApplicationBuilder(this);
        builder.setApplicability(ProofRuleApplication.Applicability.APPLICABLE);
        builder.newBranch()
                .addReplacement(selector, innerWithSubstitutions);

        return builder.build();
    }

    @Override
    public ProofRuleApplication makeApplication(ProofNode target, Parameters parameters) throws RuleException {
        checkParameters(parameters);

        throw new RuntimeException("not yet implemented"); // FIXME: Implement
    }
}
