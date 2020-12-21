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
 * You should have received a copy of the GNU General Public LicenS* along with DIVE.  If not, see <https://www.gnu.org/licenses/>.
 */

package edu.kit.iti.algover.rule.script;

import edu.kit.iti.algover.PropertyManager;
import edu.kit.iti.algover.nuscript.DefaultScriptASTVisitor;
import edu.kit.iti.algover.nuscript.ScriptAST;
import edu.kit.iti.algover.nuscript.ScriptAST.StatementList;
import edu.kit.iti.algover.nuscript.ScriptAST.Statement;
import edu.kit.iti.algover.nuscript.ScriptAST.Case;

import edu.kit.iti.algover.proof.ProofNode;
import javafx.beans.property.SimpleObjectProperty;
import javafx.concurrent.Worker;
import javafx.scene.control.Button;
import javafx.scene.control.ButtonType;
import javafx.scene.control.Dialog;
import javafx.scene.layout.HBox;
import javafx.scene.layout.Priority;
import javafx.scene.layout.VBox;
import javafx.scene.web.WebEngine;
import javafx.scene.web.WebView;

import org.w3c.dom.Document;
import org.w3c.dom.Element;

import org.w3c.dom.events.EventListener;
import org.w3c.dom.events.EventTarget;


public class BlocklyView extends VBox {
    private final WebView webView;
    private final WebEngine engine;
    private ScriptHTML scriptHTML;

    private final ScriptViewListener listener;

    private final Button btRunScript;
    private final Button btInsertCases;

    private final SimpleObjectProperty<ScriptAST> highlightedStatement = new SimpleObjectProperty<>(null);

    public BlocklyView(ScriptViewListener listener) {
        this.listener = listener;

        webView = new WebView();
        engine = webView.getEngine();

        btRunScript = new Button("Replay");
        btInsertCases = new Button("Insert cases");

        engine.setJavaScriptEnabled(true);
        engine.setOnAlert(event -> showAlert(event.getData()));

        engine.getLoadWorker().stateProperty().addListener(
                (observable, oldValue, newValue) -> {
                    if (newValue != Worker.State.SUCCEEDED) {
                        return;
                    }
                    Document doc = engine.getDocument();

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
                                public Void visitCase(Case aCase, Void arg) throws RuntimeException {
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

                                    for (StatementList c : cases.getCases()) {
                                        c.accept(this, null);
                                    }

                                    return null;
                                }


                            }, null
                    );

                }
        );


        PropertyManager.getInstance().currentProof.addListener(((observable, oldValue, newValue) -> {
            updateView();
        }));

        PropertyManager.getInstance().currentProofStatus.addListener(((observable, oldValue, newValue) -> {
            if(newValue != null) {
                /* TODO: Somehow consider filtering */

                /*  If newValue == CHANGED_SCRIPT the proof is rerun (triggered by a different listener)
                    the satus is immediately set to OPEN, CLOSED or FAILING.*/
                System.out.println("Status changed to " + newValue);
                updateView();



            }
        }));

        highlightedStatement.addListener((observable, oldValue, newValue) ->  {

            System.out.println("highlighted statement");

            System.out.println("was: " + oldValue);
            if (oldValue != null) {
                engine.executeScript("unhighlight(" + scriptHTML.getID(oldValue) + ");");
            }

            if (newValue != null) {
                engine.executeScript("highlight(" + scriptHTML.getID(newValue) + ");");
            } else {
                // TODO : search open proof node
            }

            System.out.println("is now: " + newValue);


        });

        // TODO: remove, debugging only
        PropertyManager.getInstance().currentProofNodeSelector.addListener(
                (observable, oldValue, newValue) -> {
                    System.out.println("Selected PN= " + newValue);
                }
        );

        initView();
    }

    private void initView() {

        btInsertCases.setOnAction(event -> {
            listener.onInsertCases();
        });

        HBox.setHgrow(btRunScript, Priority.ALWAYS);
        HBox.setHgrow(btInsertCases, Priority.ALWAYS);
        btRunScript.setPrefWidth(500000);
        btInsertCases.setPrefWidth(500000);
        this.getChildren().setAll(new HBox(btRunScript, btInsertCases), this.webView);
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




    private void showAlert(String message) {
        Dialog<Void> alert = new Dialog<>();
        alert.getDialogPane().setContentText(message);
        alert.getDialogPane().getButtonTypes().add(ButtonType.OK);
        alert.showAndWait();
    }

    private void updateView() {
        highlightedStatement.set(null);
        if (PropertyManager.getInstance().currentProof.get().getProofScript() != null) {
            scriptHTML = new ScriptHTML(PropertyManager.getInstance().currentProof.get().getProofScript());
            engine.loadContent(scriptHTML.getHTML());
        }
    }

}
