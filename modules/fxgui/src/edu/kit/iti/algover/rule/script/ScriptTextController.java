/*
 * Complete Refactor by Valentin Springsklee 2020
 */

package edu.kit.iti.algover.rule.script;

import edu.kit.iti.algover.PropertyManager;
import edu.kit.iti.algover.nuscript.ScriptAST;
import edu.kit.iti.algover.proof.ProofNodeSelector;
import edu.kit.iti.algover.proof.ProofStatus;
import javafx.scene.Node;

import java.util.concurrent.ExecutorService;

/**
 * Renamed from ScriptController
 */
public class ScriptTextController implements ScriptViewListener {

    final ScriptCodeView view;


    public ScriptTextController(ExecutorService higlightingExecutor) {
        view = new ScriptCodeView(higlightingExecutor, this);

        PropertyManager.getInstance().currentProofStatus.addListener(
                (observable, oldValue, newValue) -> {
                    ScriptAST.Script currentScript = PropertyManager.getInstance().currentProof.get().getProofScript();
                    if (currentScript != null) {
                        view.clear();
                        for (ScriptAST.Statement stmt : currentScript.getStatements()) {
                            view.insertText(view.getText().length(), stmt.toString() +  "\n");
                        }
                    }
                });

    }


    public Node getView() {
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


    private Void selectCommandPN(ScriptAST.Command cmd) {
        PropertyManager.getInstance().currentProofNode.set(cmd.getProofNode());
        return null;
    }

    private Void selectCasesPN(ScriptAST.Cases cases) {
        PropertyManager.getInstance().currentProofNode.set(cases.getCases().get(0).getProofNode().getChildren().get(0));
        return null;
    }

    @Override
    public void onInsertCases() {

    }
}