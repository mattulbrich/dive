/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
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

    void onResetRuleApplicationPreview();

    void onScriptSave();

    PVC getCurrentPVC();
}
