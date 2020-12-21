/*
 * This file is part of DIVE.
 *
 * DIVE is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * DIVE is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with DIVE.  If not, see <https://www.gnu.org/licenses/>.
 */

package edu.kit.iti.algover.rule.script;

import edu.kit.iti.algover.PropertyManager;
import edu.kit.iti.algover.nuscript.ScriptAST;
import edu.kit.iti.algover.nuscript.ScriptAST.Script;
import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.proof.ProofStatus;
import edu.kit.iti.algover.rules.ProofRuleApplication;
import edu.kit.iti.algover.util.ScriptASTUtil;
import edu.kit.iti.algover.util.Util;
import org.antlr.v4.runtime.CommonToken;

import java.util.ArrayList;
import java.util.List;
import java.util.logging.Logger;

public class BlocklyController implements ScriptViewListener {

    private BlocklyView view;

    public BlocklyController() {
        this.view = new BlocklyView(this);
    }

    public BlocklyView getView() {
        return view;
    }


    /**
     * Insert AST to position of display
     * @param
     * @return
     */
    public boolean insertForSelectedNode(ProofRuleApplication app, ScriptAST.Script ruleScript) {
        System.out.println("insert rule application");

        // introduced for readabilty
        ProofNode selectedPN = PropertyManager.getInstance().currentProofNode.get();
        Script currentProofScript = PropertyManager.getInstance().currentProof.get().getProofScript();

        if (selectedPN.getChildren() != null && selectedPN.getChildren().size() > 0) {
            return false;
        }

        // TODO: create ScriptAST.Statement objects from ProofRuleApplication directly
        ScriptAST.Statement ruleApplicationStatement = ruleScript.getStatements().get(0);

        Script updatedScript = ScriptASTUtil.insertAfter(currentProofScript, ruleApplicationStatement,selectedPN.getCommand());


        /*Script updatedScript = ScriptASTUtil.insertAfter(
                PropertyManager.getInstance().currentProof.get().getProofScript(),
                ruleScript.getStatements().get(0),
                highlightedStatement.get()
        );*/

        PropertyManager.getInstance().currentProof.get().setScriptAST(updatedScript);


        PropertyManager.getInstance().currentProofStatus.set(
                ProofStatus.CHANGED_SCRIPT);

        // TODO: return true iff ast added to script ast
        return false;
    }

    @Override
    public void onScriptSave() {

    }

    @Override
    public void onAsyncScriptTextChanged(String text) {

    }

    @Override
    public void runScript() {

    }

    @Override
    public void onInsertCases() {
        List<ScriptAST.Statement> updatedScript = ScriptASTUtil.insertCasesForStatement(PropertyManager.getInstance()
                        .currentProof.get().getProofRoot(),
                PropertyManager.getInstance().currentProof.get().getProofScript().getStatements());
        ScriptAST.Script newScript = ScriptASTUtil.createScriptWithStatements(updatedScript);

        PropertyManager.getInstance().currentProof.get().setScriptAST(newScript);
        PropertyManager.getInstance().currentProof.get().proofStatusObservableValue().setValue(ProofStatus.CHANGED_SCRIPT);
        PropertyManager.getInstance().currentProof.get().interpretScript();
        PropertyManager.getInstance().insertCasesPressed.set(false);
    }
}
