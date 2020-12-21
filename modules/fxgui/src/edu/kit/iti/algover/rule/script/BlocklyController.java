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
import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.proof.ProofStatus;
import edu.kit.iti.algover.rules.ProofRuleApplication;
import edu.kit.iti.algover.util.ScriptASTUtil;
import edu.kit.iti.algover.util.Util;
import javafx.beans.property.SimpleObjectProperty;
import javafx.concurrent.Worker;
import org.antlr.v4.runtime.CommonToken;
import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.events.EventListener;
import org.w3c.dom.events.EventTarget;

import java.util.ArrayList;
import java.util.List;
import java.util.logging.Logger;

public class BlocklyController implements ScriptViewListener {

    private BlocklyView view;
    private final SimpleObjectProperty<ScriptAST> highlightedStatement = new SimpleObjectProperty<>(null);
    private ScriptHTML scriptHTML;

    public BlocklyController() {
        this.view = new BlocklyView(this);
        configureListeners();

    }

    private void configureListeners() {
        view.getEngine().getLoadWorker().stateProperty().addListener(
                (observable, oldValue, newValue) -> {
                    if (newValue != Worker.State.SUCCEEDED) {
                        return;
                    }
                    Document doc = view.getEngine().getDocument();

                    // add listeners to HTML

                    PropertyManager.getInstance().currentProof.get().getProofScript().accept(
                            new DefaultScriptASTVisitor<Void, Void, RuntimeException>() {

                                @Override
                                protected void visitStatements(ScriptAST.StatementList statementList, Void arg) throws RuntimeException {
                                    Integer elemID = scriptHTML.getID(statementList);
                                    addHTMLElemListeners(doc, elemID, evt -> {
                                        evt.stopPropagation();
                                        // TODO: CSS highlighting
                                        highlightedStatement.set(statementList);

                                        PropertyManager.getInstance().currentProofNode.set(
                                                statementList.accept(new ProofNodeExtractionVisitor(), null)
                                        );
                                    });

                                    super.visitStatements(statementList, arg);
                                }

                                @Override
                                public Void visitCase(ScriptAST.Case aCase, Void arg) throws RuntimeException {
                                    visitStatements(aCase, arg);
                                    return null;
                                }

                                @Override
                                public Void visitCommand(ScriptAST.Command command, Void arg) throws RuntimeException {
                                    addHTMLElemListeners(doc, scriptHTML.getID(command), evt -> {
                                        evt.stopPropagation();
                                        highlightedStatement.set(command);
                                        PropertyManager.getInstance().currentProofNode.set(command.getProofNode());

                                    });
                                    return null;
                                }


                                @Override
                                public Void visitCases(ScriptAST.Cases cases, Void arg) throws RuntimeException {
                                    addHTMLElemListeners(doc, scriptHTML.getID(cases), evt -> {
                                        evt.stopPropagation();
                                        highlightedStatement.set(cases);
                                        PropertyManager.getInstance().currentProofNode.
                                                set(cases.getCases().get(0).getProofNode());
                                    });

                                    for (ScriptAST.StatementList c : cases.getCases()) {
                                        c.accept(this, null);
                                    }

                                    return null;
                                }


                            }, null
                    );

                }
        );

        highlightedStatement.addListener((observable, oldValue, newValue) ->  {

            System.out.println("highlighted statement");

            System.out.println("was: " + oldValue);
            if (oldValue != null) {
                view.getEngine().executeScript("unhighlight(" + scriptHTML.getID(oldValue) + ");");
            }

            if (newValue != null) {
                view.getEngine().executeScript("highlight(" + scriptHTML.getID(newValue) + ");");
            } else {
                // TODO : search open proof node
            }

            System.out.println("is now: " + newValue);


        });


        PropertyManager.getInstance().currentProof.addListener(((observable, oldValue, newValue) -> {
            if (PropertyManager.getInstance().currentProof.get().getProofScript() != null) {
                scriptHTML = new ScriptHTML(PropertyManager.getInstance().currentProof.get().getProofScript());
                view.update(scriptHTML.getHTML());
            }
        }));

        PropertyManager.getInstance().currentProofStatus.addListener(((observable, oldValue, newValue) -> {
            if(newValue != null) {
                /* TODO: Somehow consider filtering */

                /*  If newValue == CHANGED_SCRIPT the proof is rerun (triggered by a different listener)
                    the satus is immediately set to OPEN, CLOSED or FAILING.*/
                System.out.println("Status changed to " + newValue);
                if (PropertyManager.getInstance().currentProof.get().getProofScript() != null) {
                    scriptHTML = new ScriptHTML(PropertyManager.getInstance().currentProof.get().getProofScript());
                    view.update(scriptHTML.getHTML());
                }
            }
        }));

    }

    private void addHTMLElemListeners(Document doc, Integer id, EventListener listener) {
        if (id == null) {
            return;
        }
        Element el = doc.getElementById(String.valueOf(id));
        // TODO: remove listener ?
        if (el != null) {
            // useCapture parameter of addEventListener method influences the direction of event propagation.
            // See HTML/JavaScript specification for exact description.
            // For HTML documents: true ~ top down, false ~ bottom up
            ((EventTarget) el).addEventListener("click", listener, false);
        } else {
            System.out.println("Statement with id " + id + " not found in HTMl Document.");
        }
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
    }
}
