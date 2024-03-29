/*
 * Complete Refactor by Valentin Springsklee 2020
 */

package edu.kit.iti.algover.rule.script;

import edu.kit.iti.algover.PropertyManager;
import edu.kit.iti.algover.nuscript.ScriptAST;
import edu.kit.iti.algover.proof.Proof;
import edu.kit.iti.algover.proof.ProofNodeSelector;
import edu.kit.iti.algover.proof.ProofStatus;
import edu.kit.iti.algover.util.ExceptionDialog;
import javafx.beans.property.SimpleObjectProperty;
import javafx.scene.Node;
import javafx.scene.layout.Region;
import org.antlr.v4.runtime.NoViableAltException;
import org.antlr.v4.runtime.misc.ParseCancellationException;

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
                view.clear();
                view.insertText(0, newValue.getScriptText());
                runScript();
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


    public ScriptCodeView getView() {
        return view;
    }

    @Override
    public void runScript() {
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