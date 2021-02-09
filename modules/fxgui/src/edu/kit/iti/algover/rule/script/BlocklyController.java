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
import javafx.beans.property.SimpleObjectProperty;
import javafx.scene.input.KeyCode;

import java.util.List;

public class BlocklyController implements ScriptViewListener {

    private BlocklyView view;
    private final SimpleObjectProperty<ScriptAST> highlightedStatement = new SimpleObjectProperty<>(null);

    public BlocklyController() {
        this.view = new BlocklyView(this);
        configureListeners();
    }

    /**
     * Add event listeners to the html components that represent the
     * individual AST elements.
     * Listeners handle proof node selection
     */
    private void configureListeners() {

        highlightedStatement.addListener((observable, oldValue, newValue) ->  {
            if (oldValue != null) {
                view.unhighlight(oldValue);
            }
            if (newValue != null) {
                view.highlight(newValue);
            }
            view.requestFocus();
        });

        PropertyManager.getInstance().currentProof.addListener(((observable, oldValue, newValue) -> {
            if (newValue != null) {
                if (newValue.getProofScript() != null) {
                    // TODO: (maybe) select open end
                    highlightedStatement.set(null);
                }
            }

            view.update();

        }));

        PropertyManager.getInstance().currentProofNode.addListener((observable, oldValue, newValue) ->
        {
            if (newValue != null) {
                 if (newValue == PropertyManager.getInstance().currentProof.get().getProofRoot()) {
                     if (PropertyManager.getInstance().currentProof.get().getProofScript() != null &&
                         PropertyManager.getInstance().currentProof.get().getProofScript().getStatements().size() == 0) {
                         highlightedStatement.set(PropertyManager.getInstance().currentProof.get().getProofScript());

                     }
                 } else if (!(newValue == null || newValue.getCommand() == null)) {
                     if (newValue.getChildren() == null || newValue.getChildren().size() == 0) {
                         ScriptAST.StatementList parentList = (ScriptAST.StatementList) newValue.getCommand().getParent();
                         /*if (parentList.getStatements().size() <= 0 ) {
                             highlightedStatement.set(PropertyManager.getInstance().currentProof.get().getProofScript());
                         }*/

                         if (newValue.getCommand() == parentList.getStatements().get(parentList.getStatements().size() - 1)) {
                             highlightedStatement.set(parentList);
                         } else {
                             for (int i = 0; i < parentList.getStatements().size(); i++) {
                                 ScriptAST.Statement stmt = parentList.getStatements().get(i);
                                 if (stmt == newValue.getCommand()) {
                                     ScriptAST.Statement nextStmt = parentList.getStatements().get(i + 1);
                                     ScriptAST.Cases cases = (ScriptAST.Cases) nextStmt;
                                     for (int j = 0; j < newValue.getParent().getChildren().size(); j++) {
                                         // TODO: tests and assertions
                                         // Handle implicit cases
                                         ProofNode pChild = newValue.getParent().getChildren().get(j);
                                         if (pChild == newValue) {
                                             if (j < cases.getCases().size()) {
                                                 highlightedStatement.set(cases.getCases().get(j));
                                             }
                                             return;
                                         }
                                     }
                                 }
                             }
                         }

                         //highlightedStatement.set(newValue.getCommand().getParent());
                     } else {
                         //highlightedStatement.set(newValue.getChildren().get(0).getCommand());
                     }
                 }
            }

        });

        view.setOnKeyPressed(event -> {
            if (event.getCode() == KeyCode.BACK_SPACE) {
                PropertyManager.getInstance().currentProof.get().setScriptAST(
                        ScriptASTUtil.removeStatementFromScript(PropertyManager.getInstance().currentProof.get().getProofScript(),
                                highlightedStatement.get()));
            }

            PropertyManager.getInstance().currentProof.get().interpretScript();

        });

        PropertyManager.getInstance().currentProofStatus.addListener(((observable, oldValue, newValue) -> {
            if(PropertyManager.getInstance().currentProof.get() != null) {
                /* TODO: Somehow consider filtering newValue*/
                /*  If newValue == CHANGED_SCRIPT the proof is rerun (triggered by a different listener)
                    the satus is immediately set to OPEN, CLOSED or FAILING.*/

                Script currentScript = PropertyManager.getInstance().currentProof.get().getProofScript();

                view.update();

                if (currentScript != null) {
                    if (currentScript.getStatements().isEmpty()) {
                        PropertyManager.getInstance().currentProofNode.set(
                                PropertyManager.getInstance().currentProof.get().getProofRoot()
                        );
                    }
                }
            }
        }));
    }

    private void scanProofEnds(ScriptAST.StatementList script) {
        if (script == null) {
            return;
        }
        ProofNode pn = script.accept(ProofNodeExtractionVisitor.INSTANCE, null);
        if (pn != null) {
            if (pn.isClosed()) {
                view.setClosedProofEnd(script);
            }
        }

        boolean caseOpen = false;
        boolean casesInList = false;
        for (ScriptAST.Statement stmt : script.getStatements()) {
            if (stmt instanceof ScriptAST.Cases) {
                casesInList = true;
                ScriptAST.Cases cases = (ScriptAST.Cases) stmt;
                for (ScriptAST.Case aCase : cases.getCases()) {
                    scanProofEnds(aCase);
                }
                ProofNode splitting = cases.accept(ProofNodeExtractionVisitor.INSTANCE, null).getParent();
                if (splitting.getChildren().size() > cases.getCases().size()) {
                    caseOpen = true;
                }
            }
        }

        if (casesInList && !caseOpen) {
            view.hideProofEnd(script);
        }

    }


    public BlocklyView getView() {
        return view;
    }


    /**
     * Insert AST to position of display
     * @param app
     * @param ruleScript parsed app
     * Parameters redundant
     */
    public void insertAtCurrentPosition(ProofRuleApplication app, ScriptAST.Script ruleScript) {
        // introduced for readabilty
        Script currentProofScript = PropertyManager.getInstance().currentProof.get().getProofScript();

        if (highlightedStatement.get() == null) {
            return;
        }

        // TODO: create from ProofRuleApplication, also look at RuleApplicationController for that.
        ScriptAST.Statement newStatement = ruleScript.getStatements().get(0);

        Script updatedScript = ScriptASTUtil.insertStatementAfter(currentProofScript, newStatement,
               highlightedStatement.getValue());

        PropertyManager.getInstance().currentProof.get().setScriptAST(updatedScript);
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

        Script updated = new Script();
        updated.addStatements(updatedScript);

        PropertyManager.getInstance().currentProof.get().setScriptAST(updated);
        PropertyManager.getInstance().currentProof.get().interpretScript();
    }

    @Override
    public void onViewReloaded() {
        ProofStatus proofState = PropertyManager.getInstance().currentProofStatus.get();
        if (proofState == ProofStatus.OPEN || proofState == ProofStatus.CLOSED) {
            scanProofEnds(PropertyManager.getInstance().currentProof.get().getProofScript());
        }

        view.highlight(highlightedStatement.get());

    }

    @Override
    public void onASTElemSelected(ScriptAST astElem) {
        highlightedStatement.set(astElem);
        ProofNode displayNode = astElem.accept(ProofNodeExtractionVisitor.INSTANCE, null);
        PropertyManager.getInstance().currentProofNode.set(displayNode);
    }

    @Override
    public SimpleObjectProperty<ScriptAST> getHighlightedElemProperty() {
        return highlightedStatement;
    }

}
