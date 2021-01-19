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
import edu.kit.iti.algover.proof.Proof;
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

    private final ScriptViewListener listener;

    private final Button btRunScript;
    private final Button btInsertCases;

    private ScriptHTML scriptHTML;

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

                    PropertyManager.getInstance().currentProof.get().getProofScript().accept(
                            new DefaultScriptASTVisitor<Void, Void, RuntimeException>() {

                                @Override
                                protected Void visitDefault(ScriptAST ast, Void arg) throws RuntimeException {
                                    return null;
                                }

                                @Override
                                protected void visitStatements(ScriptAST.StatementList statementList, Void arg) throws RuntimeException {
                                    visitDefault(statementList, arg);
                                    for (ScriptAST.Statement statement : statementList.getStatements()) {
                                        statement.accept(this, arg);
                                    }
                                }

                                @Override
                                public Void visitCommand(ScriptAST.Command command, Void arg) throws RuntimeException {
                                    Integer elemID = scriptHTML.getID(command);
                                    addHTMLElemListeners(doc, elemID, evt -> {
                                        evt.stopPropagation();
                                        listener.onASTElemSelected(command);
                                    });
                                    return null;
                                }

                                @Override
                                public Void visitCases(ScriptAST.Cases cases, Void arg) throws RuntimeException {
                                    Integer elemID = scriptHTML.getID(cases);
                                    addHTMLElemListeners(doc, elemID, evt -> {
                                        evt.stopPropagation();
                                        listener.onASTElemSelected(cases);
                                    });
                                    for (ScriptAST.Case aCase : cases.getCases()) {
                                        aCase.accept(this, arg);
                                    }
                                    return null;
                                }

                                @Override
                                public Void visitCase(ScriptAST.Case caze, Void arg) throws RuntimeException {
                                    Integer elemID = scriptHTML.getID(caze);
                                    addHTMLElemListeners(doc, elemID, evt -> {
                                        evt.stopPropagation();
                                        listener.onASTElemSelected(caze);
                                    });
                                    return null;
                                }


                            }, null
                    );
                }
        );

        engine.getLoadWorker().stateProperty().addListener((observable, oldValue, newValue) -> {
            if (newValue == Worker.State.SUCCEEDED) {
                highlight(listener.getHighlightedElemProperty().get());
            }
        });

        initView();
        update();
    }

    private void addHTMLElemListeners(Document doc, Integer id, EventListener listener) {
        if (id == null) {
            // TODO: logging
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
            // TODO: log somewhere (not for user)
            System.out.println("Statement with id " + id + " not found in HTMl Document.");
        }
    }


    private void initView() {

        btInsertCases.setOnAction(event -> listener.onInsertCases());

        HBox.setHgrow(btRunScript, Priority.ALWAYS);
        HBox.setHgrow(btInsertCases, Priority.ALWAYS);
        btRunScript.setPrefWidth(500000);
        btInsertCases.setPrefWidth(500000);
        this.getChildren().setAll(new HBox(btRunScript, btInsertCases), this.webView);
    }

    private void showAlert(String message) {
        Dialog<Void> alert = new Dialog<>();
        alert.getDialogPane().setContentText(message);
        alert.getDialogPane().getButtonTypes().add(ButtonType.OK);
        alert.showAndWait();
    }

    public void update() {
        Proof currentProof = PropertyManager.getInstance().currentProof.get();
        if (currentProof != null) {
            scriptHTML = new ScriptHTML(PropertyManager.getInstance().currentProof.get().getProofScript());
            engine.loadContent(scriptHTML.getHTML());
        }
    }


    public void highlight(ScriptAST astElem) {
        Integer elemid = scriptHTML.getID(astElem);
        if (elemid != null) {
            engine.executeScript("highlight(" + elemid+ ");");
        }
    }

    public void unhighlight(ScriptAST astElem) {
        Integer elemid = scriptHTML.getID(astElem);
        if (elemid != null) {
            engine.executeScript("unhighlight(" + elemid + ");");
        }

    }

}
