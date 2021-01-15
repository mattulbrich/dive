/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.rule.script;

import edu.kit.iti.algover.nuscript.ScriptAST;
import javafx.beans.property.SimpleObjectProperty;

// TODO: rename. Should also pose as an interface for
// necessary data
public interface ScriptViewListener {

    void onScriptSave();

    void onAsyncScriptTextChanged(String text);

    void runScript();

    void onInsertCases();

    void onASTElemSelected(ScriptAST astElem);

    // TODO: review
    SimpleObjectProperty<ScriptAST> getHighlightedElemProperty();

}
