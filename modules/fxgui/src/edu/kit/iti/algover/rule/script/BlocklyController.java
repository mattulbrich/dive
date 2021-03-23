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

import antlr.RecognitionException;
import edu.kit.iti.algover.PropertyManager;
import edu.kit.iti.algover.nuscript.DefaultScriptASTVisitor;
import edu.kit.iti.algover.nuscript.ScriptAST;
import edu.kit.iti.algover.nuscript.ScriptAST.Script;
import edu.kit.iti.algover.nuscript.ScriptException;
import edu.kit.iti.algover.nuscript.UnsealedCopyVisitor;
import edu.kit.iti.algover.proof.Proof;
import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.proof.ProofNodeSelector;
import edu.kit.iti.algover.proof.ProofStatus;
import edu.kit.iti.algover.rules.DafnyRuleException;
import edu.kit.iti.algover.rules.ProofRuleApplication;
import edu.kit.iti.algover.rules.RuleException;
import edu.kit.iti.algover.util.ExceptionDetails;
import edu.kit.iti.algover.util.ExceptionDialog;
import edu.kit.iti.algover.util.ScriptASTUtil;
import javafx.beans.property.SimpleObjectProperty;
import javafx.scene.input.KeyCode;
import javafx.scene.input.KeyEvent;
import org.antlr.v4.runtime.misc.ParseCancellationException;

import java.util.ArrayList;
import java.util.List;
import java.util.logging.Logger;

public class BlocklyController implements ScriptViewListener {

    private BlocklyView view;

    /**
     * This property hols the AST element in the current proof script (currentProof.getProofScript())
     * that is selected for highlighting in the BlocklyView.
     */
    private final SimpleObjectProperty<ScriptAST> highlightedASTElement = new SimpleObjectProperty<>(null);

    private Script beforeStep;

    public BlocklyController() {
        this.view = new BlocklyView(this);
        beforeStep = null;
        configureListeners();
    }

    /**
     * Add event listeners to the html components that represent the
     * individual AST elements.
     * Listeners handle proof node selection
     */
    private void configureListeners() {

        highlightedASTElement.addListener((observable, oldValue, newValue) ->  {
            if (oldValue != null) {
                view.unhighlight(oldValue);
            }
            if (newValue != null) {
                view.highlight(newValue);
            }
        });

        PropertyManager.getInstance().currentProof.addListener((observable, oldValue, newValue) -> view.update());

        PropertyManager.getInstance().currentProofNode.addListener((observable, oldValue, newValue) ->
                reconsiderHighlighting(newValue));

        view.addEventFilter(KeyEvent.KEY_PRESSED, event -> {

            if (event.isControlDown() && event.getCode() == KeyCode.Z) {
                // undo script
                if (beforeStep != null) {
                    runScript();

                    highlightedASTElement.set(getHighlightFromProofNodeSelector(
                            PropertyManager.getInstance().currentProofNodeSelector.get()));
                    beforeStep = null;

                }
                return;
            }

            if (highlightedASTElement.get() != null) {
                if (event.getCode() == KeyCode.BACK_SPACE) {
                    // remove selected element
                    // whole list if leaf (last pn in list) is selected
                    ScriptAST newHighlight = highlightedASTElement.get();
                    Proof currentProof = PropertyManager.getInstance().currentProof.get();
                    Script updatedScript = ScriptASTUtil.removeStatementFromScript(
                            currentProof.getProofScript(), highlightedASTElement.get());
                    beforeStep = UnsealedCopyVisitor.INSTANCE.visitScript(
                            PropertyManager.getInstance().currentProof.get().getProofScript(), null);


                    PropertyManager.getInstance().currentProof.get().setScriptAST(updatedScript);
                    runScript();

                    newHighlight = getHighlightFromProofNodeSelector(
                           PropertyManager.getInstance().currentProofNodeSelector.get());
                    highlightAndSetProofNode(newHighlight);
                    event.consume();
                    view.requestFocus();
                    return;
                } else {
                    // TODO: catch invalid ProofNodes
                    if (event.getCode() == KeyCode.DOWN) {
                        ScriptAST newHighlight = highlightedASTElement.get().accept(NavigateDownVisitor.INSTANCE, null);
                        highlightAndSetProofNode(newHighlight);
                        event.consume();
                        view.requestFocus();
                    } else if (event.getCode() == KeyCode.UP) {
                        ScriptAST newHighlight = highlightedASTElement.get().accept(NavigateUpVisitor.INSTANCE, null);
                        highlightAndSetProofNode(newHighlight);
                        event.consume();
                        view.requestFocus();
                    }
                }
            }
        });

        PropertyManager.getInstance().currentProofStatus.addListener(((observable, oldValue, newValue) -> {
            if(PropertyManager.getInstance().currentProof.get() != null) {
                view.update();
                Script currentScript = PropertyManager.getInstance().currentProof.get().getProofScript();

                if (currentScript != null) {
                    if (currentScript.getStatements().isEmpty()) {
                        PropertyManager.getInstance().currentProofNode.set(
                                PropertyManager.getInstance().currentProof.get().getProofRoot()
                        );
                        highlightedASTElement.set(PropertyManager.getInstance().currentProof.get().getProofScript());
                    }
                }

                if (newValue == ProofStatus.OPEN || newValue == ProofStatus.CLOSED) {
                    ProofNodeSelector currentSelector = PropertyManager.getInstance().currentProofNodeSelector.get();
                    Logger.getGlobal().info("Successfully ran script.");
                    if (currentSelector != null) {
                        ProofNode afap = currentSelector.followAsFarAsPossible(
                                PropertyManager.getInstance().currentProof.get().getProofRoot());
                        PropertyManager.getInstance().currentProofNode.set(afap.getParent());
                        PropertyManager.getInstance().currentProofNode.set(afap);

                    }
                }

            }
        }));
    }

    @Override
    public void runScript() {
        Proof proof = PropertyManager.getInstance().currentProof.get();
        Script proofScript = PropertyManager.getInstance().currentProof.get().getProofScript();
        // (!proofScript.isSealed()) ==> (ProofStatus == CHANGED)
        if (proofScript != null && proofScript.isSealed()) {
            // error
            return;
        }
        proof.setScriptAST(proofScript);
        proof.interpretScript();
    }

    private void highlightScriptErrors(List<Exception> exceptions) {
        for (Exception ex: exceptions) {
            createErrorReport(ex);
        }
    }

    /**
     * Highlight the exceptions that occurred upon the last interpretation
     * of the script of {@link PropertyManager#currentProof} in Blockly
     */
    public void highlightScriptErrors() {
        Proof proof = PropertyManager.getInstance().currentProof.get();
        highlightScriptErrors(proof.getFailures());
    }

    private void createErrorReport(Throwable ex) {
        if (ex instanceof RuleException) {
            ExceptionDialog ed = new ExceptionDialog(ex);
            ed.showAndWait();
        } else if (ex instanceof ScriptException) {
            ScriptException scriptException = (ScriptException) ex;
            ScriptAST errorAST = scriptException.getScriptAST();
            view.highlightError(errorAST);
            ExceptionDialog ed = new ExceptionDialog(ex);
            ed.showAndWait();
        } else if (ex instanceof ParseCancellationException) {
            ExceptionDialog ed = new ExceptionDialog(ex);
            ed.showAndWait();
        } else if (ex instanceof RecognitionException) {
            ExceptionDialog ed = new ExceptionDialog(ex);
            ed.showAndWait();
        } else if (ex instanceof DafnyRuleException) {
            ExceptionDialog ed = new ExceptionDialog(ex);
            ed.showAndWait();
        } else {
            ExceptionDialog ed = new ExceptionDialog(ex);
            ed.showAndWait();
        }
    }


    private void reconsiderHighlighting(ProofNode newValue) {
        if (newValue != null) {
            if (newValue == PropertyManager.getInstance().currentProof.get().getProofRoot()) {
                if (PropertyManager.getInstance().currentProof.get().getProofScript() != null &&
                        PropertyManager.getInstance().currentProof.get().getProofScript().getStatements().size() == 0) {
                    highlightedASTElement.set(PropertyManager.getInstance().currentProof.get().getProofScript());

                }
            } else if (!(newValue == null || newValue.getCommand() == null)) {
                if (newValue.getChildren() == null || newValue.getChildren().size() == 0) {
                    ScriptAST newHighlight = ScriptASTUtil.getASTListFromPN(newValue);
                    highlightedASTElement.set(newHighlight);
                } else {
                    ScriptAST.StatementList parent = (ScriptAST.StatementList) ScriptASTUtil.getASTListFromPN(newValue);
                    if (newValue.getCommand().getParent() != parent) {
                        highlightedASTElement.set(parent.getStatements().get(0));
                    }
                }
            }
        }
    }

    /**
     * prototypic to sort nested Exception (from ScriptException)
     * ASTVisitor should locate failing parameter
     * @param ex
     */
    private void propagateScriptException(ScriptException ex) {
        ScriptAST errorAST = ex.getScriptAST();
        Throwable cause = ex.getCause();
        if (ex != cause) {
            if (cause instanceof RuleException) {
                String message = cause.getMessage();
                ScriptAST detailedError = errorAST.accept(new DefaultScriptASTVisitor<String, ScriptAST, IllegalArgumentException>() {
                    @Override
                    public ScriptAST visitCommand(ScriptAST.Command command, String arg) throws IllegalArgumentException {
                        for (ScriptAST.Parameter p: command.getParameters()) {
                            final String schemaKey = "Schematic sequent ";
                            if (arg.startsWith(schemaKey)) {
                                String schemaSeq = arg.substring(schemaKey.length());
                                //String prettyPrinted = schemaSeq.
                                if (p.getValue().toString().contains(schemaSeq)) {
                                    return p;
                                }
                            }
                        }
                        return null;
                    }
                }, message);

                view.highlightError(detailedError);

            }
        }

    }

    private void highlightAndSetProofNode(ScriptAST toHighlight) {
        if (toHighlight != null) {
            PropertyManager.getInstance().currentProofNode.set(
                    toHighlight.accept(ProofNodeExtractionVisitor.INSTANCE, null));
        }
        highlightedASTElement.set(toHighlight);
    }



    private ScriptAST getHighlightFromProofNodeSelector(ProofNodeSelector selector) {
        if (selector == null) {
            return null;
        }
        ScriptAST highlight = null;
        ProofNode displayedNode = selector.followAsFarAsPossible(PropertyManager.getInstance().currentProof.get().getProofRoot());
        if (displayedNode.getChildren() != null) {
            if (displayedNode.getChildren().size() > 0) {
                highlight = displayedNode.getChildren().get(0).getCommand();
            } else {
                // TODO: handle error node
                if (displayedNode.getParent() != null) {
                    highlight = displayedNode.getParent().getCommand();
                }
            }
        } else { // open end
            if (displayedNode.getCommand() == null) {
                // assert proof root
                highlight = PropertyManager.getInstance().currentProof.get().getProofScript();
            } else {
                // Statement List or last statement of it
                highlight = ScriptASTUtil.getASTListFromPN(displayedNode);

            }
        }

        return highlight;

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
                // assert non empty cases
                if (splitting.getChildren() != null) {
                    if (splitting.getChildren().size() > cases.getCases().size()) {
                        caseOpen = true;
                    }
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

        if (highlightedASTElement.get() == null) {
            return;
        }

        // TODO: create from ProofRuleApplication, also look at RuleApplicationController for that.
        ScriptAST.Statement newStatement = ruleScript.getStatements().get(0);

        Script updatedScript = ScriptASTUtil.insertStatementAfter(currentProofScript, newStatement,
               highlightedASTElement.getValue());

        beforeStep = UnsealedCopyVisitor.INSTANCE.visitScript(
                PropertyManager.getInstance().currentProof.get().getProofScript(), null);
        PropertyManager.getInstance().currentProof.get().setScriptAST(updatedScript);
    }

    @Override
    public void onInsertCases() {
        Script updated = null;
        try {
            updated = ScriptASTUtil.insertMissingCases(PropertyManager.getInstance()
                            .currentProof.get().getProofRoot(),
                    PropertyManager.getInstance().currentProof.get().getProofScript());
        } catch (ScriptException e) {
            highlightScriptErrors();
        }

        beforeStep = UnsealedCopyVisitor.INSTANCE.visitScript(
                PropertyManager.getInstance().currentProof.get().getProofScript(), null);

        PropertyManager.getInstance().currentProof.get().setScriptAST(updated);
        runScript();

        ProofNode currentPN = PropertyManager.getInstance().currentProofNode.get();
        PropertyManager.getInstance().currentProofNode.set(currentPN.getParent());
        PropertyManager.getInstance().currentProofNode.set(currentPN);
    }

    @Override
    public void onViewReloaded() {
        ProofStatus proofState = PropertyManager.getInstance().currentProofStatus.get();
        if (proofState == ProofStatus.OPEN || proofState == ProofStatus.CLOSED) {
            scanProofEnds(PropertyManager.getInstance().currentProof.get().getProofScript());
        } else if (proofState == ProofStatus.FAILING) {
            highlightScriptErrors();
        }

        view.highlight(highlightedASTElement.get());

    }

    @Override
    public void onASTElemSelected(ScriptAST astElem) {
        highlightedASTElement.set(astElem);
        ProofNode displayNode = astElem.accept(ProofNodeExtractionVisitor.INSTANCE, null);
        try {
            ProofNodeSelector pns = new ProofNodeSelector(displayNode);
            PropertyManager.getInstance().currentProofNodeSelector.set(pns);
        } catch (RuntimeException rex) {

        }

    }

}
