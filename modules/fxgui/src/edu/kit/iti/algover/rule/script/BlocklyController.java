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
import edu.kit.iti.algover.nuscript.UnsealedCopyVisitor;
import edu.kit.iti.algover.proof.Proof;
import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.proof.ProofNodeSelector;
import edu.kit.iti.algover.proof.ProofStatus;
import edu.kit.iti.algover.rules.ProofRuleApplication;
import edu.kit.iti.algover.util.ScriptASTUtil;
import javafx.beans.property.SimpleObjectProperty;
import javafx.scene.input.KeyCode;
import javafx.scene.input.KeyEvent;

import java.util.List;

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

        PropertyManager.getInstance().currentProof.addListener(((observable, oldValue, newValue) -> {
            view.update();
        }));

        PropertyManager.getInstance().currentProofNode.addListener((observable, oldValue, newValue) ->
        {
            if (newValue != null) {
                 if (newValue == PropertyManager.getInstance().currentProof.get().getProofRoot()) {
                     if (PropertyManager.getInstance().currentProof.get().getProofScript() != null &&
                         PropertyManager.getInstance().currentProof.get().getProofScript().getStatements().size() == 0) {
                         highlightedASTElement.set(PropertyManager.getInstance().currentProof.get().getProofScript());

                     }
                 } else if (!(newValue == null || newValue.getCommand() == null)) {
                     if (newValue.getChildren() == null || newValue.getChildren().size() == 0) {
                         highlightedASTElement.set(findCaseEnd(newValue));
                     } else {
                         ScriptAST.StatementList parent = (ScriptAST.StatementList) findCaseEnd(newValue);
                         highlightedASTElement.set(parent.getStatements().get(0));
                     }
                 }
            }

        });

        view.addEventFilter(KeyEvent.KEY_PRESSED, event -> {

            if (event.isControlDown() && event.getCode() == KeyCode.Z) {
                if (beforeStep != null) {
                    PropertyManager.getInstance().currentProof.get().setScriptAST(beforeStep);
                    PropertyManager.getInstance().currentProof.get().interpretScript();
                    highlightedASTElement.set(getHighlightFromProofNodeSelector(
                            PropertyManager.getInstance().currentProofNodeSelector.get()));
                    beforeStep = null;

                }
                return;
            }

            if (highlightedASTElement.get() != null) {
                if (event.getCode() == KeyCode.BACK_SPACE) {
                    ScriptAST newHighlight = highlightedASTElement.get();

                    Proof currentProof = PropertyManager.getInstance().currentProof.get();
                    Script updatedScript = ScriptASTUtil.removeStatementFromScript(
                            currentProof.getProofScript(), highlightedASTElement.get());
                    beforeStep = UnsealedCopyVisitor.INSTANCE.visitScript(
                            PropertyManager.getInstance().currentProof.get().getProofScript(), null);

                    currentProof.setScriptAST(updatedScript);

                    if (currentProof.getProofStatus() == ProofStatus.CHANGED_SCRIPT) {
                        currentProof.interpretScript();
                        newHighlight = getHighlightFromProofNodeSelector(
                                PropertyManager.getInstance().currentProofNodeSelector.get());

                        highlightAndSetProofNode(newHighlight);
                    }
                    event.consume();
                    view.requestFocus();
                    return;
                } else {
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
                        highlightedASTElement.set(PropertyManager.getInstance().currentProof.get().getProofScript());
                    }
                }
            }
        }));
    }

    private void highlightAndSetProofNode(ScriptAST toHighlight) {
        if (toHighlight != null) {
            PropertyManager.getInstance().currentProofNode.set(
                    toHighlight.accept(ProofNodeExtractionVisitor.INSTANCE, null));
        }
        highlightedASTElement.set(toHighlight);
    }

    private ScriptAST findCaseEnd(ProofNode displayedNode) {
        ScriptAST.StatementList parentList = (ScriptAST.StatementList) displayedNode.getCommand().getParent();
        ScriptAST highlight = parentList;
        for (int i = 0; i < parentList.getStatements().size() - 1; i++) {
            ScriptAST.Statement stmt = parentList.getStatements().get(i);
            if (stmt == displayedNode.getCommand()) {
                ScriptAST.Statement nextStmt = parentList.getStatements().get(i + 1);
                // Use visitor?
                if (nextStmt instanceof ScriptAST.Cases) {
                    ScriptAST.Cases cases = (ScriptAST.Cases) nextStmt;
                    for (int j = 0; j < displayedNode.getParent().getChildren().size(); j++) {
                        // TODO: tests and assertions
                        // Handle implicit cases
                        ProofNode pChild = displayedNode.getParent().getChildren().get(j);
                        if (pChild == displayedNode) {
                            if (j < cases.getCases().size()) {
                                return cases.getCases().get(j);
                            }
                        }
                    }
                } else {
                    return displayedNode.getCommand().getParent();
                }
            }
        }
        return highlight;
    }


    private ScriptAST getHighlightFromProofNodeSelector(ProofNodeSelector selector) {
        System.out.println("Current node: " + PropertyManager.getInstance().currentProofNodeSelector.get());
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
                highlight = findCaseEnd(displayedNode);

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

        beforeStep = UnsealedCopyVisitor.INSTANCE.visitScript(
                PropertyManager.getInstance().currentProof.get().getProofScript(), null);        PropertyManager.getInstance().currentProof.get().setScriptAST(updated);
        PropertyManager.getInstance().currentProof.get().interpretScript();
    }

    @Override
    public void onViewReloaded() {
        ProofStatus proofState = PropertyManager.getInstance().currentProofStatus.get();
        if (proofState == ProofStatus.OPEN || proofState == ProofStatus.CLOSED) {
            scanProofEnds(PropertyManager.getInstance().currentProof.get().getProofScript());
        }

        view.highlight(highlightedASTElement.get());

    }

    @Override
    public void onASTElemSelected(ScriptAST astElem) {
        highlightedASTElement.set(astElem);
        ProofNode displayNode = astElem.accept(ProofNodeExtractionVisitor.INSTANCE, null);
        PropertyManager.getInstance().currentProofNode.set(displayNode);
    }

}
