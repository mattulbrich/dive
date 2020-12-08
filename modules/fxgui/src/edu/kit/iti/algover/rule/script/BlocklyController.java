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
import edu.kit.iti.algover.nuscript.ScriptAST.Statement;
import edu.kit.iti.algover.nuscript.ScriptAST.Cases;
import edu.kit.iti.algover.nuscript.ScriptAST.Case;

import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.proof.ProofNodeSelector;
import edu.kit.iti.algover.proof.ProofStatus;
import edu.kit.iti.algover.rules.ProofRuleApplication;
import javafx.beans.property.SimpleObjectProperty;
import javafx.concurrent.Worker;
import javafx.scene.control.ButtonType;
import javafx.scene.control.Dialog;
import javafx.scene.web.WebEngine;
import javafx.scene.web.WebView;
import org.w3c.dom.Document;
import org.w3c.dom.Element;

import org.w3c.dom.events.EventTarget;
import java.util.List;

public class BlocklyController {
    private final WebView view;
    private final WebEngine engine;
    private Document doc;

    private final SimpleObjectProperty<ScriptAST.Statement> highlightedStatement = new SimpleObjectProperty<>(null);


    private ScriptHTML scriptHTML;


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
                    recursivelyAddListeners(doc, PropertyManager.getInstance().currentProof.get().getProofScript().getStatements());
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


    }

    public WebView getView() {
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

    private void recursivelyAddListeners(Document doc, List<ScriptAST.Statement> statements) {
        for(Statement stmt : statements) {
            stmt.visit(command -> {
                addListener(doc, command);
                return null;
            }, cases -> {
                addListener(doc, cases);
                for (Case caze: cases.getCases()) {
                    recursivelyAddListeners(doc, caze.getStatements());
                }
                return null;
            });
        }
    }

    private void addListener(Document doc, Statement cmd) {
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

    public void addCasesListener(Document doc, Cases cases) {
        Element el = doc.getElementById(scriptHTML.getID(cases).toString());
        // TODO: remove listener ?
        if (el != null) {
            ((EventTarget) el).addEventListener("click", event -> {
                if (highlightedStatement.get() == cases) {
                    highlightedStatement.set(null);
                    return;
                }
                highlightedStatement.set(cases);
            }, false);
        } else {
            System.out.println("Statement: " + cases + " not found in AST Display.");
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
