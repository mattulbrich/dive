package edu.kit.iti.algover.rule;

import edu.kit.iti.algover.data.SymbolTable;
import edu.kit.iti.algover.proof.PVC;
import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.proof.ProofNodeSelector;
import edu.kit.iti.algover.rule.script.ScriptViewListener;
import edu.kit.iti.algover.rules.ProofRule;
import edu.kit.iti.algover.rules.ProofRuleApplication;
import edu.kit.iti.algover.rules.TermSelector;

public interface RuleApplicationListener {
    void onPreviewRuleApplication(ProofRuleApplication application);

    void onRuleApplication(ProofRuleApplication application);

    void onRuleExApplication(ProofRule rule, TermSelector ts);

    void onResetRuleApplicationPreview();

    void onSwitchViewedNode(ProofNodeSelector selector);

    void onScriptSave();

    PVC getCurrentPVC();

    ProofNode getCurrentProofNode();
}
