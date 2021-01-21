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
import edu.kit.iti.algover.nuscript.DefaultScriptASTVisitor;
import edu.kit.iti.algover.nuscript.ScriptAST;
import edu.kit.iti.algover.nuscript.ScriptAST.Script;
import edu.kit.iti.algover.proof.Proof;
import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.rules.ProofRuleApplication;
import edu.kit.iti.algover.util.Pair;
import edu.kit.iti.algover.util.ScriptASTUtil;
import javafx.beans.property.SimpleObjectProperty;

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
        });

        PropertyManager.getInstance().currentProof.addListener(((observable, oldValue, newValue) -> {
            System.out.println("Proof changed");
            if (newValue.getProofScript() != null) {
                // TODO: (maybe) select open end
                //highlightedStatement.set(null);
                view.update();
            }
        }));

        PropertyManager.getInstance().currentProofNode.addListener((observable, oldValue, newValue) ->
        {
            if (newValue != null) {
                 if (newValue == PropertyManager.getInstance().currentProof.get().getProofRoot()) {
                     highlightedStatement.set(PropertyManager.getInstance().currentProof.get().getProofScript());
                 } else if (!(newValue == null || newValue.getCommand() == null)) {
                     if (newValue.getChildren() == null || newValue.getChildren().size() == 0) {
                         ScriptAST.StatementList parentList = newValue.getCommand().getParent().accept(
                                 new DefaultScriptASTVisitor<Void, ScriptAST.StatementList, IllegalArgumentException>() {
                                     @Override
                                     public ScriptAST.StatementList visitScript(Script script, Void arg) throws IllegalArgumentException {
                                         return script;
                                     }

                                     @Override
                                     public ScriptAST.StatementList visitCase(ScriptAST.Case aCase, Void arg) throws IllegalArgumentException {
                                         return aCase;
                                     }
                                 }
                         , null);

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
                                         ProofNode pChild = newValue.getParent().getChildren().get(i);
                                         if (pChild == newValue) {
                                             highlightedStatement.set(cases.getCases().get(j));
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

        PropertyManager.getInstance().currentProofStatus.addListener(((observable, oldValue, newValue) -> {
            System.out.println("Proof Status changed to " + newValue);

            if(newValue != null) {
                /* TODO: Somehow consider filtering newValue*/
                /*  If newValue == CHANGED_SCRIPT the proof is rerun (triggered by a different listener)
                    the satus is immediately set to OPEN, CLOSED or FAILING.*/

                Script currentScript = PropertyManager.getInstance().currentProof.get().getProofScript();

                if (currentScript != null) {
                    if (currentScript.getStatements().size() == 0) {
                        PropertyManager.getInstance().currentProofNode.set(
                                PropertyManager.getInstance().currentProof.get().getProofRoot()
                        );
                    }
                }

                view.update();
            }
        }));
    }


    public BlocklyView getView() {
        return view;
    }


    /**
     * Insert AST to position of display
     * @param
     * @return
     */
    public boolean insertAtCurrentPosition(ProofRuleApplication app, ScriptAST.Script ruleScript) {
        // introduced for readabilty
        ProofNode selectedPN = PropertyManager.getInstance().currentProofNode.get();
        Script currentProofScript = PropertyManager.getInstance().currentProof.get().getProofScript();
        if (selectedPN.getChildren() != null && selectedPN.getChildren().size() > 0) {
            return false;
        }

        if (highlightedStatement.get() == null) {
            return false;
        }

        // TODO: create ScriptAST.Statement objects from ProofRuleApplication directly
        ScriptAST.Statement ruleApplicationStatement = ruleScript.getStatements().get(0);

        Script updatedScript = highlightedStatement.get().accept(new DefaultScriptASTVisitor<Pair<Script, ScriptAST.Statement>, Script, RuntimeException>() {
            @Override
            public Script visitCommand(ScriptAST.Command command, Pair<Script, ScriptAST.Statement> arg) throws RuntimeException {
                return arg.getFst();
            }

            @Override
            public Script visitCases(ScriptAST.Cases cases, Pair<Script, ScriptAST.Statement> arg) throws RuntimeException {
                return arg.getFst();
            }

            @Override
            public Script visitCase(ScriptAST.Case aCase, Pair<Script, ScriptAST.Statement> arg) throws RuntimeException {
                Script updated = ScriptASTUtil.insertIntoCase(arg.getFst(), arg.getSnd(), aCase);
                return updated;
            }

            /**
             * TODO: review. Check legality here?
             * @param script
             * @param arg
             * @return
             * @throws RuntimeException
             */
            @Override
            public Script visitScript(Script script, Pair<Script, ScriptAST.Statement> arg) throws RuntimeException {
                List<ScriptAST.Statement> stmts = script.getStatements();
                stmts.add(arg.getSnd());
                Script updatedScript = ScriptASTUtil.createScriptWithStatements(stmts);
                return updatedScript;
            }
        }, new Pair<>(currentProofScript, ruleApplicationStatement));

        boolean scriptChanged = currentProofScript.equals(updatedScript);

        PropertyManager.getInstance().currentProof.get().setScriptAST(updatedScript);

        //return true iff ast added to script ast
        return scriptChanged;
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
        PropertyManager.getInstance().currentProof.get().interpretScript();
    }

    @Override
    public void onASTElemSelected(ScriptAST astElem) {
        highlightedStatement.set(astElem);
        PropertyManager.getInstance().currentProofNode.set(
                astElem.accept(new ProofNodeExtractionVisitor(), null)
        );
    }

    @Override
    public SimpleObjectProperty<ScriptAST> getHighlightedElemProperty() {
        return highlightedStatement;
    }

}
