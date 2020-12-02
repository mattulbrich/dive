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
import edu.kit.iti.algover.nuscript.ScriptAST.Command;
import edu.kit.iti.algover.nuscript.ScriptAST.Statement;
import edu.kit.iti.algover.nuscript.ScriptAST.Cases;
import edu.kit.iti.algover.nuscript.ScriptAST.Case;

import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.proof.ProofNodeSelector;
import edu.kit.iti.algover.rules.ProofRuleApplication;
import edu.kit.iti.algover.rules.RuleApplicator;
import edu.kit.iti.algover.term.builder.TermBuildException;
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

    private List<ProofNodeCheckpoint> checkpoints;


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
            if(newValue != null) {
                checkpoints = ProofNodeCheckpoint.extractCheckpoints(newValue);
                updateView();
            }
        }));

        PropertyManager.getInstance().currentProofStatus.addListener(((observable, oldValue, newValue) -> {
            if(newValue != null) {
                /* TODO: Somehow consider filtering */

                /*  If newValue == CHANGED_SCRIPT the proof is rerun (triggered by a different listener)
                    the satus is immediately set to OPEN, CLOSED or FAILING.*/
                System.out.println("Status changed to " + newValue);
                checkpoints = ProofNodeCheckpoint.extractCheckpoints(PropertyManager.getInstance().currentProof.get());
                updateView();
            }
        }));

        highlightedStatement.addListener((observable, oldValue, newValue) ->  {

            if (oldValue != null) {
                engine.executeScript("unhighlight(" + oldValue.hashCode() + ")");
            }

            if (newValue != null) {
                engine.executeScript("highlight(" + newValue.hashCode() + ")");
                handleProofNodeSelection(newValue);
            } else {
                ProofNode openPN = null;
                for (ProofNodeCheckpoint cp : checkpoints) {
                    if (cp.getType() == ProofNodeCheckpoint.Type.OPEN) {
                        openPN = cp.getProofNode();
                        break;
                    }
                }

                PropertyManager.getInstance().currentProofNode.set(openPN);
            }
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
        for (ProofNodeCheckpoint cp : checkpoints) {
            if (cp.getType() == ProofNodeCheckpoint.Type.OPEN) {
                if (cp.getProofNode().equals(PropertyManager.getInstance().currentProofNode.get())) {
                    System.out.println("Match: " + cp.getAst());
                    // TODO : visitor
                    ScriptAST branch = cp.getAst();
                    if (branch instanceof Script) {
                        for (Statement stmt : ruleScript.getStatements()) {
                            ((Script) branch).addStatement(stmt);
                        }
                    } else if (branch instanceof Case) {
                        for (Statement stmt : ruleScript.getStatements()) {
                            ((Case) branch).addStatement(stmt);
                        }
                    }

                }
                System.out.println("No match" + cp.getAst() + " btw pns are selected" +
                        PropertyManager.getInstance().currentProofNodeSelector
                        + " cp: " + new ProofNodeSelector(cp.getProofNode()));
            }
        }



        // TODO: return true iff ast added to script ast
        return true;
    }

    private void recursivelyAddListeners(Document doc, List<ScriptAST.Statement> statements) {
        for(Statement stmt : statements) {
            stmt.visit(command -> {
                addListenerCommand(doc, command);
                return null;
            }, cases -> {
                for (Case caze: cases.getCases()) {
                    recursivelyAddListeners(doc, caze.getStatements());
                }
                return null;
            });
        }
    }

    private void addListenerCommand(Document doc, ScriptAST.Command cmd) {
        Element el = doc.getElementById(String.valueOf(cmd.hashCode()));
        // TODO: remove listener ?
        if (el != null) {
            ((EventTarget) el).addEventListener("click", event -> {
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

    private boolean handleProofNodeSelection(ScriptAST.Statement statement) {
        ProofNode afterStatement = statement.visit(this::commandProofNode, this::casesProofNode);
        PropertyManager.getInstance().currentProofNode.set(afterStatement);

        /* TODO : review relationship (statement - proof node) in checkpoint
            and create more performant mapping */
        /*for (ProofNodeCheckpoint checkpoint : checkpoints) {
            if (checkpoint.getAst().equals(statement) && checkpoint.isEndOfAst()) {
                System.out.println("Found corr");
                PropertyManager.getInstance().currentProofNode.set(checkpoint.getProofNode());
                //break;

            }
        }*/

        return true;
    }

    private ProofNode commandProofNode(ScriptAST.Command cmd) {
        ProofNode pn = cmd.getProofNode();
        if (pn == null) {
            pn = PropertyManager.getInstance().currentProof.get().getProofRoot();
        }
        if (pn.getChildren() == null) {
            return pn;
        }
        System.out.println("Num children of select node: " + pn.getChildren().size());
        ProofNode ret = pn.getChildren().get(0);
        assert (ret != null);
        return ret;
    }

    // TODO
    private ProofNode casesProofNode(ScriptAST.Cases cases) {
        ProofNode pn = cases.getCases().get(0).getProofNode();

        List<ProofNode> pnchildren = pn.getChildren();

        assert pnchildren.size() == cases.getCases().size();

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
            String content = ProofHTML.toHTML(PropertyManager.getInstance().currentProof.get().getProofScript());
            engine.loadContent(content);
            System.out.println("recreatedsv");
            for (ProofNodeCheckpoint checkpoint: checkpoints) {
                System.out.println(checkpoint);
            }

        }
    }

}
