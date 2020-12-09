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
import edu.kit.iti.algover.nuscript.parser.ScriptParser;
import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.proof.ProofStatus;
import edu.kit.iti.algover.rules.ProofRuleApplication;
import edu.kit.iti.algover.util.ScriptASTUtil;
import edu.kit.iti.algover.util.Util;
import org.antlr.v4.runtime.CommonToken;

import java.util.ArrayList;
import java.util.List;
import java.util.logging.Logger;

public class BlocklyController {

    private BlocklyView view;

    public BlocklyController() {
        this.view = new BlocklyView();

        PropertyManager.getInstance().insertCasesPressed.addListener((observable, oldValue, newValue) -> {
            if (newValue == true) {
                List<ScriptAST.Statement> updatedScript = insertCasesForStatement(PropertyManager.getInstance()
                                .currentProof.get().getProofRoot(),
                        PropertyManager.getInstance().currentProof.get().getProofScript().getStatements());
                ScriptAST.Script newScript = ScriptASTUtil.createScriptWithStatements(updatedScript);

                PropertyManager.getInstance().currentProof.get().setScriptAST(newScript);
                PropertyManager.getInstance().currentProof.get().proofStatusObservableValue().setValue(ProofStatus.CHANGED_SCRIPT);
                PropertyManager.getInstance().currentProof.get().interpretScript();
                PropertyManager.getInstance().insertCasesPressed.set(false);
            }

        });

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
        // TODO: return true iff ast added to script ast
        return false;
    }


    /**
     * recursivly inserts all missing case statements in the given script
     *
     * @param pn the proofnode for which the cases should be inserted
     * @param stmts the current script that should be extended by the missing case statements
     * @return a new script containing all necessary case statements
     */
    // MU: Adapted the existing code to nuscript. But it does not seem to be recursive at all.
    private List<ScriptAST.Statement> insertCasesForStatement(ProofNode pn, List<ScriptAST.Statement> stmts) {
        if(stmts.size() == 0) {
            return stmts;
        }
        List<ScriptAST.Statement> result = new ArrayList<>();
        for (int i = 0; i < stmts.size() - 1; ++i) {
            if(stmts.get(i) instanceof ScriptAST.Command) {
                result.add(stmts.get(i));
            } else {
                Logger.getGlobal().warning("Only the last statement may be a cases-statement.");
                return stmts;
            }
            if((pn.getChildren() != null && pn.getChildren().size() == 1)) {
                pn = pn.getChildren().get(0);
            } else if (stmts.size() - 2 != i) {
                Logger.getGlobal().warning("Script has unexpected number of children at some point.");
                return stmts;
            }
        }
        ScriptAST.Statement st = stmts.get(stmts.size() - 1);
        if(pn.getSuccessors().size() == 1 && st instanceof ScriptAST.Command) {
            result.add(st);
        } else if (pn.getChildren().size() > 1 && st instanceof ScriptAST.Cases) {
            result.add(createCasesForNode(pn, ((ScriptAST.Cases) st).getCases()));
        } else if (pn.getChildren().size() > 1 && !(st instanceof ScriptAST.Cases)) {
            result.add(st);
            result.add(createCasesForNode(pn));
        }

        return result;
    }

    /**@
     * Creates all cases for the given proofnode except the ones given in cases
     *
     * @param pn the proofnode for which the cases should be created
     * @param cases the cases that already exist
     * @return a case statement containing all necesarry cases
     */
    private ScriptAST.Statement createCasesForNode(ProofNode pn, List<ScriptAST.Case> cases) {
        ScriptAST.Cases res = new ScriptAST.Cases();
        for(ProofNode p : pn.getChildren()) {
            boolean found = false;
            for(ScriptAST.Case caze : cases) {
                //apparently some guards are string literals and some are MathcExpressions...
                String caseString = Util.stripQuotes(caze.getLabel().getText());
                if (caseString.equals(p.getLabel())) {
                    List<ScriptAST.Statement> statements = insertCasesForStatement(p, caze.getStatements());
                    caze.addStatements(statements);
                    res.getCases().add(caze);
                    found = true;
                }
            }
            if(!found) {
                ScriptAST.Case c = new ScriptAST.Case();
                c.setLabel(new CommonToken(ScriptParser.STRING_LITERAL, "\"" + p.getLabel() + "\""));
                res.getCases().add(c);
            }
        }
        return res;
    }

    private ScriptAST.Statement createCasesForNode(ProofNode pn) {
        return createCasesForNode(pn, new ArrayList<>());
    }
}
