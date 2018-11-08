package edu.kit.iti.algover.rules.impl;

import edu.kit.iti.algover.data.BuiltinSymbols;
import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.proof.ProofNodeSelector;
import edu.kit.iti.algover.rules.AbstractProofRule;
import edu.kit.iti.algover.rules.Parameters;
import edu.kit.iti.algover.rules.ProofRule;
import edu.kit.iti.algover.rules.ProofRuleApplication;
import edu.kit.iti.algover.rules.ProofRuleApplicationBuilder;
import edu.kit.iti.algover.rules.RuleApplicator;
import edu.kit.iti.algover.rules.RuleException;
import edu.kit.iti.algover.rules.SubtermSelector;
import edu.kit.iti.algover.rules.TermParameter;
import edu.kit.iti.algover.rules.TermSelector;
import edu.kit.iti.algover.term.ApplTerm;
import edu.kit.iti.algover.term.FunctionSymbol;
import edu.kit.iti.algover.term.Sort;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.term.builder.TermBuildException;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;
import java.util.Optional;
import java.util.stream.Collectors;

/**
 * Created by jklamroth on 11/7/18.
 */
public class IntegerSimplification extends AbstractProofRule {
    private final List<Class> applicableRuleTypes = new ArrayList<Class>(Arrays.asList(PlusZeroRule.class,
            TimesOneRule.class, TimesZeroRule.class));
    private List<AbstractProofRule> applicableRules;

    public IntegerSimplification() {
        super(ON_PARAM);
    }

    @Override
    public String getName() {
        return "times1";
    }

    @Override
    protected ProofRuleApplication considerApplicationImpl(ProofNode target, Parameters parameters) throws RuleException {
        applicableRules = target.getPVC().getProject().getAllProofRules().stream().
                filter(proofRule -> applicableRuleTypes.contains(proofRule.getClass())).
                map(proofRule -> (AbstractProofRule)proofRule).
                collect(Collectors.toList());

        ProofRuleApplicationBuilder proofRuleApplicationBuilder = new ProofRuleApplicationBuilder(this);
        proofRuleApplicationBuilder.newBranch();
        proofRuleApplicationBuilder.setSubApplications(Collections.singletonList(transitiveApplication(target, parameters)));

        return proofRuleApplicationBuilder.build();
    }

    @Override
    protected ProofRuleApplication makeApplicationImpl(ProofNode target, Parameters parameters) throws RuleException {
        ProofRuleApplication pra = considerApplication(target, parameters);
        if(pra.getApplicability() != ProofRuleApplication.Applicability.APPLICABLE) {
            throw new RuleException("TimesOneRule is not applicable in make");
        }
        return pra;
    }

    ProofRuleApplication addToSubApps(ProofRuleApplication root, ProofRuleApplication sub) {
        if(root.getSubApplications() == null || root.getSubApplications().size() == 0 || root.getSubApplications().get(0) == null) {
            ProofRuleApplicationBuilder prab = new ProofRuleApplicationBuilder(root);
            prab.setSubApplications(new ArrayList<>(Collections.singletonList(sub)));
            return prab.build();
        } else {
            ProofRuleApplicationBuilder prab = new ProofRuleApplicationBuilder(root);
            prab.setSubApplications(new ArrayList<>(
                    Collections.singletonList(addToSubApps(root.getSubApplications().get(0), sub))));
            return prab.build();
        }
    }

    ProofRuleApplication singleStep1(ProofNode target, Parameters parameters) throws RuleException {
        for(AbstractProofRule r : applicableRules) {
            ProofRuleApplication pra = r.considerApplication(target, parameters);
            if(pra.getApplicability() == ProofRuleApplication.Applicability.APPLICABLE) {
                return pra;
            }
        }
        TermParameter onParam = parameters.getValue(ON_PARAM);
        for(int i = 0; i < onParam.getTerm().getSubterms().size(); ++i) {
            Parameters params = new Parameters();
            params.putValue("on", new TermParameter(new TermSelector(onParam.getTermSelector(), i), target.getSequent()));
            ProofRuleApplication p = singleStep1(target, params);
            if(p != null) {
                return p;
            }
        }
        return null;
    }

    ProofRuleApplication transitiveApplication(ProofNode target, Parameters parameters) throws RuleException {
        ProofRuleApplication res = singleStep1(target, parameters);
        ProofRuleApplication pra = res;
        while(pra != null) {
            List<ProofNode> newNodes = RuleApplicator.applyRule(pra, target);
            //No closing or branching rules allowed!
            assert(newNodes.size() == 1);
            target = newNodes.get(0);
            while(target.getChildren().size() > 0) {
                assert(target.getChildren().size() == 1);
                target = target.getChildren().get(0);
            }
            Parameters params = new Parameters();
            params.putValue("on", new TermParameter(new TermSelector(parameters.getValue(ON_PARAM).getTermSelector()), target.getSequent()));
            pra = singleStep1(target, params);
            if(pra != null) {
                res = addToSubApps(res, pra);
            }
        }
        return res;
    }
}
