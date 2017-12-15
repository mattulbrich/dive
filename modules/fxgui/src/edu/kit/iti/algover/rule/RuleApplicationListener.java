package edu.kit.iti.algover.rule;

import edu.kit.iti.algover.rules.ProofRuleApplication;

public interface RuleApplicationListener {
    void onPreviewRuleApplication(ProofRuleApplication application);

    void onRuleApplication(ProofRuleApplication application);
}
