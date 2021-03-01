/*
 * Complete Refactor by Valentin Springsklee 2020
 */

package edu.kit.iti.algover.rule.script;

import edu.kit.iti.algover.PropertyManager;
import edu.kit.iti.algover.nuscript.ScriptAST;
import edu.kit.iti.algover.proof.Proof;
import edu.kit.iti.algover.proof.ProofNodeSelector;
import edu.kit.iti.algover.proof.ProofStatus;
import javafx.beans.property.SimpleObjectProperty;
import javafx.scene.Node;
import javafx.scene.layout.Region;

import java.util.concurrent.ExecutorService;

/**
 * Renamed from ScriptController
 */
public class ScriptTextController implements ScriptViewListener {

    final ScriptCodeView view;


    public ScriptTextController(ExecutorService higlightingExecutor) {
        view = new ScriptCodeView(higlightingExecutor, this);

        PropertyManager.getInstance().currentProof.addListener((observable, oldValue, newValue) -> {
            if (newValue == null) {
                view.setDisable(true);
            } else {
                view.setDisable(false);
            }
        });

        PropertyManager.getInstance().currentProofStatus.addListener(
                (observable, oldValue, newValue) -> {
                    if (PropertyManager.getInstance().currentProof.get() != null) {
                        ScriptAST.Script currentScript = PropertyManager.getInstance().currentProof.get().getProofScript();
                        if (currentScript != null) {
                            view.clear();
                            for (ScriptAST.Statement stmt : currentScript.getStatements()) {
                                view.insertText(view.getText().length(), stmt.toString() + "\n");
                            }
                        }
                    } else {
                        view.clear();
                    }
                });

    }


    public Region getView() {
        return view;
    }


    @Override
    public void onScriptSave() {
        // TODO: parse script and build AST
    }

    @Override
    public void onAsyncScriptTextChanged(String text) {

    }

    @Override
    public void runScript() {
        // TODO: save and run
        String scriptStr = view.getText();
        PropertyManager.getInstance().currentProof.get().setScriptText(scriptStr);
        PropertyManager.getInstance().currentProof.get().interpretScript();


    }

    @Override
    public void onInsertCases() {

    }

    @Override
    public void onViewReloaded() {

    }

    @Override
    public void onASTElemSelected(ScriptAST astElem) {

    }
}