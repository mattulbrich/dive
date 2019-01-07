package edu.kit.iti.algover.rules.impl;

import edu.kit.iti.algover.data.BuiltinSymbols;
import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.rules.AbstractProofRule;
import edu.kit.iti.algover.rules.Parameters;
import edu.kit.iti.algover.rules.ProofRuleApplication;
import edu.kit.iti.algover.rules.ProofRuleApplicationBuilder;
import edu.kit.iti.algover.rules.RuleException;
import edu.kit.iti.algover.rules.SubtermSelector;
import edu.kit.iti.algover.rules.TermParameter;
import edu.kit.iti.algover.rules.TermSelector;
import edu.kit.iti.algover.term.ApplTerm;
import edu.kit.iti.algover.term.FunctionSymbol;
import edu.kit.iti.algover.term.Sort;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.term.builder.TermBuildException;

/**
 * Created by jklamroth on 11/7/18.
 */
public class TimesZeroRule extends AbstractProofRule {

    public TimesZeroRule() {
        super(ON_PARAM);
    }

    @Override
    public String getName() {
        return "times0";
    }

    @Override
    protected ProofRuleApplication considerApplicationImpl(ProofNode target, Parameters parameters) throws RuleException {
        TermParameter onParam = parameters.getValue(ON_PARAM);
        if(onParam == null) {
            return ProofRuleApplicationBuilder.notApplicable(this);
        }
        Term onTerm = onParam.getTerm();
        if(!(onTerm instanceof ApplTerm)) {
            return ProofRuleApplicationBuilder.notApplicable(this);
        }

        ApplTerm applTerm = (ApplTerm)onTerm;
        if(applTerm.getFunctionSymbol() != BuiltinSymbols.TIMES && applTerm.getFunctionSymbol() != BuiltinSymbols.DIV) {
            return ProofRuleApplicationBuilder.notApplicable(this);
        }

        try {
            if (!applTerm.getTerm(0).equals(new ApplTerm(new FunctionSymbol("0", Sort.INT))) &&
                    !applTerm.getTerm(1).equals(new ApplTerm(new FunctionSymbol("0", Sort.INT)))) {
                return ProofRuleApplicationBuilder.notApplicable(this);
            } else {
                ProofRuleApplicationBuilder prab = new ProofRuleApplicationBuilder(this);
                prab.newBranch().addReplacement(onParam.getTermSelector(), new ApplTerm(new FunctionSymbol("0", Sort.INT)));
                return prab.build();
            }
        } catch (TermBuildException e) {
            throw new RuleException("This should not happen. Error building constants in PlusZeroRule.");
        }
    }

    @Override
    protected ProofRuleApplication makeApplicationImpl(ProofNode target, Parameters parameters) throws RuleException {
        ProofRuleApplication pra = considerApplication(target, parameters);
        if(pra.getApplicability() != ProofRuleApplication.Applicability.APPLICABLE) {
            throw new RuleException("TimesOneRule is not applicable in make");
        }
        return pra;
    }
}
