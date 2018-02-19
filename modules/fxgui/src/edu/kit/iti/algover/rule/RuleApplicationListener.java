package edu.kit.iti.algover.rule;

import edu.kit.iti.algover.rule.script.ScriptViewListener;
import edu.kit.iti.algover.rules.ProofRuleApplication;

public interface RuleApplicationListener extends ScriptViewListener {
    void onPreviewRuleApplication(ProofRuleApplication application);

    void onRuleApplication(ProofRuleApplication application);

    void onResetRuleApplicationPreview();
}
