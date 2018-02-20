package edu.kit.iti.algover.rule;

import edu.kit.iti.algover.proof.ProofNodeSelector;
import edu.kit.iti.algover.rule.script.ScriptViewListener;
import edu.kit.iti.algover.rules.ProofRuleApplication;

public interface RuleApplicationListener {
    void onPreviewRuleApplication(ProofRuleApplication application);

    void onRuleApplication(ProofRuleApplication application);

    void onResetRuleApplicationPreview();

    void onSwitchViewedNode(ProofNodeSelector selector);

    void onScriptSave();
}
