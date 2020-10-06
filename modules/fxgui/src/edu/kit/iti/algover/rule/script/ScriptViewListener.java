/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.rule.script;

public interface ScriptViewListener {

    void onScriptSave();

    void onAsyncScriptTextChanged(String text);

    void runScript();

    void onInsertCases();
}
