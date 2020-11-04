/*
 * This file is part of DIVE.
 *
 * DIVE is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * Foobar is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with Foobar.  If not, see <https://www.gnu.org/licenses/>.
 */

package edu.kit.iti.algover.rule.script;

import edu.kit.iti.algover.PropertyManager;
import edu.kit.iti.algover.nuscript.ScriptAST;
import edu.kit.iti.algover.proof.ProofNodeSelector;
import javafx.concurrent.Worker;
import javafx.scene.control.ButtonType;
import javafx.scene.control.Dialog;
import javafx.scene.web.WebEngine;
import javafx.scene.web.WebView;
import org.w3c.dom.Document;
import org.w3c.dom.Element;

import org.w3c.dom.events.EventTarget;

public class BlocklyController {
    private final WebView view;
    private final WebEngine engine;
    private Document doc;

    private ScriptAST.Statement highlightedStatement = null;

    public BlocklyController() {
        view = new WebView();
        engine = view.getEngine();

        engine.setJavaScriptEnabled(true);
        engine.setOnAlert(event -> showAlert(event.getData()));

        engine.getLoadWorker().stateProperty().addListener(
                (observable, oldValue, newValue) -> {
                    if (newValue != Worker.State.SUCCEEDED) {
                        return;
                    }
                    doc = engine.getDocument();

                    for(ScriptAST.Statement stmt :
                            PropertyManager.getInstance().currentProof.get().getProofScript().getStatements()) {
                        Element el = doc.getElementById(String.valueOf(stmt.hashCode()));
                        // TODO: remove listener ?
                        ((EventTarget) el).addEventListener("click", event -> {
                            if (highlightedStatement != null) {
                                engine.executeScript("unhighlight(" + highlightedStatement.hashCode() + ")");
                            }
                            handleProofNodeSelection(stmt);
                            highlightedStatement = stmt;
                        }, false);
                    }

                }
        );


        PropertyManager.getInstance().currentProof.addListener(((observable, oldValue, newValue) -> {
            if(newValue != null) {
                updateView();
            }
        }));

        PropertyManager.getInstance().currentProofStatus.addListener(((observable, oldValue, newValue) -> {
            if(newValue != null) {
                updateView();
            }
        }));
    }

    public WebView getView() {
        return view;
    }

    private boolean handleProofNodeSelection(ScriptAST.Statement statement) {
        ScriptAST.Script script = PropertyManager.getInstance().currentProof.get().getProofScript();
        ScriptAST.Statement stmtNext;
        if (script.getStatements().indexOf(statement) + 1 < script.getStatements().size()) {
            stmtNext = script.getStatements().get(script.getStatements().indexOf(statement) + 1);
        } else {
            stmtNext = statement;
        }
        stmtNext.visit(this::commandProofNode, this::casesProofNode);

        engine.executeScript("highlight(" + statement.hashCode() + ")");

        return true;
    }

    private Void commandProofNode(ScriptAST.Command cmd) {

        PropertyManager.getInstance().currentProofNodeSelector.set(new ProofNodeSelector(cmd.getProofNode()));
        return null;
    }

    // TODO
    private Void casesProofNode(ScriptAST.Cases cases) {
       // PropertyManager.getInstance().currentProofNode.set(cases.getCases());
        return null;

    }

    private void showAlert(String message) {
        Dialog<Void> alert = new Dialog<>();
        alert.getDialogPane().setContentText(message);
        alert.getDialogPane().getButtonTypes().add(ButtonType.OK);
        alert.showAndWait();
    }

    private void updateView() {
        highlightedStatement = null;
        if (PropertyManager.getInstance().currentProof.get().getProofScript() != null) {
            String content = ProofHTML.toHTML(PropertyManager.getInstance().currentProof.get().getProofScript());
            engine.loadContent(content);
        }
    }

}
