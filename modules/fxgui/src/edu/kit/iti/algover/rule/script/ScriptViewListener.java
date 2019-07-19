/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.rule.script;

import edu.kit.iti.algover.script.ast.ProofScript;

public interface ScriptViewListener {

    void onScriptSave();

    void onAsyncScriptTextChanged(String text);

    void runScript();

    String onInsertCases();
}
