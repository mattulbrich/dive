package edu.kit.iti.algover.rule.script;

import edu.kit.iti.algover.script.ast.ProofScript;

public interface ScriptViewListener {

    void onScriptSave();
    void onAsyncScriptTextChanged(String text);
}
