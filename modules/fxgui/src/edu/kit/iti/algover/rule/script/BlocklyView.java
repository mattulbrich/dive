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

import org.w3c.dom.events.EventTarget;

import java.util.List;

public class BlocklyView extends VBox {
    private final WebView webView;
    private final WebEngine engine;
    private Document doc;
    private ScriptHTML scriptHTML;

    private final Button btRunScript;
    private final Button btInsertCases;


    private final SimpleObjectProperty<ScriptAST.Statement> highlightedStatement = new SimpleObjectProperty<>(null);


    public BlocklyView() {
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
                    doc = engine.getDocument();
                    recursivelyAddListeners(doc, PropertyManager.getInstance().currentProof.get().getProofScript());
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
                engine.executeScript("unhighlight(" + scriptHTML.getID(oldValue) + ")");
            }

            if (newValue != null) {
                engine.executeScript("highlight(" + scriptHTML.getID(newValue) + ")");
                handleProofNodeSelection(newValue);
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
            PropertyManager.getInstance().insertCasesPressed.setValue(true);
        });

        HBox.setHgrow(btRunScript, Priority.ALWAYS);
        HBox.setHgrow(btInsertCases, Priority.ALWAYS);
        btRunScript.setPrefWidth(500000);
        btInsertCases.setPrefWidth(500000);
        this.getChildren().setAll(new HBox(btRunScript, btInsertCases), this.webView);
    }

    // TODO: assert not null, vistor for script and case
    private void recursivelyAddListeners(Document doc, ScriptAST.Script proofScript) {

        List<Statement> statements = proofScript.getStatements();

        if (statements.size() == 0) {
            return;
        }

        for(Statement stmt : statements) {
            stmt.visit(command -> {
                addHTMLElemListeners(doc, command);
                return null;
            }, cases -> {
                addHTMLElemListeners(doc, cases);
                for (Case caze: cases.getCases()) {
                    recursivelyAddListeners(doc, caze);
                }
                return null;
            });
        }


        addLeafListener(doc, proofScript);
    }

    // TODO: Add visitor for Script or Case
    private void recursivelyAddListeners(Document doc, ScriptAST.Case c) {

        List<Statement> statements = c.getStatements();

        if (statements.size() == 0) {
            return;
        }

        for(Statement stmt : statements) {
            stmt.visit(command -> {
                addHTMLElemListeners(doc, command);
                return null;
            }, cases -> {
                addHTMLElemListeners(doc, cases);
                for (Case caze: cases.getCases()) {
                    recursivelyAddListeners(doc, caze);
                }
                return null;
            });
        }


        addLeafListener(doc, c);
    }

    private void addHTMLElemListeners(Document doc, Statement cmd) {
        Element el = doc.getElementById(scriptHTML.getID(cmd).toString());
        // TODO: remove listener ?
        if (el != null) {
            // useCapture parameter of addEventListener method influences the direction of event propagation.
            // See HTML/JavaScript specification for exact description.
            // For HTML documents: true ~ top down, false ~ bottom up
            ((EventTarget) el).addEventListener("click", event -> {
                event.stopPropagation();
                if (highlightedStatement.get() == cmd) {
                    highlightedStatement.set(null);
                    return;
                }
                highlightedStatement.set(cmd);
            }, false);
        } else {
            System.out.println("Statement: " + cmd + " not found in AST Display.");
        }
    }

    private void addLeafListener(Document doc, ScriptAST container) {
        Integer id = scriptHTML.getID(container);
        if (id == null) {
            System.out.println("No leaf");
            return;
        }
        Element el = doc.getElementById(String.valueOf(id));
        // TODO: remove listener ?
        if (el != null) {
            // useCapture parameter of addEventListener method influences the direction of event propagation.
            // See HTML/JavaScript specification for exact description.
            // For HTML documents: true ~ top down, false ~ bottom up
            ((EventTarget) el).addEventListener("click", event -> {
                System.out.println("Leaf clicked");
                event.stopPropagation();
                engine.executeScript("highlight(" + id + ")");
            }, false);
        } else {
            System.out.println("Statement: " + container + " not found in AST Display.");
        }
    }

    private boolean handleProofNodeSelection(ScriptAST.Statement statement) {
        ProofNode afterStatement = statement.visit(this::commandProofNode, this::casesProofNode);
        PropertyManager.getInstance().currentProofNode.set(afterStatement);

        return true;
    }

    private ProofNode commandProofNode(ScriptAST.Command cmd) {
        ProofNode pn = cmd.getProofNode();
        return pn;
    }

    // TODO
    private ProofNode casesProofNode(ScriptAST.Cases cases) {
        ProofNode pn = cases.getCases().get(0).getProofNode();

        return pn;

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
