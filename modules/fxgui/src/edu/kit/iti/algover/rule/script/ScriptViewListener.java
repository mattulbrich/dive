/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.rule.script;

import edu.kit.iti.algover.nuscript.ScriptAST;

public interface ScriptViewListener {

    void runScript();

    void onInsertCases();

    void onViewReloaded();

    void onASTElemSelected(ScriptAST astElem);

}
