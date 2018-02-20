package edu.kit.iti.algover.rule.script;

import edu.kit.iti.algover.proof.Proof;
import edu.kit.iti.algover.proof.ProofNodeSelector;
import edu.kit.iti.algover.rule.RuleApplicationListener;
import edu.kit.iti.algover.script.ast.Position;
import edu.kit.iti.algover.script.ast.ProofScript;
import edu.kit.iti.algover.util.RuleApp;
import javafx.beans.Observable;
import javafx.concurrent.Task;
import org.fxmisc.richtext.model.StyleSpans;

import java.time.Duration;
import java.util.Collection;
import java.util.List;
import java.util.Optional;
import java.util.concurrent.ExecutorService;
import java.util.function.Consumer;

public class ScriptController implements ScriptViewListener {

    private final ScriptView view;
    private final RuleApplicationListener listener;

    private Proof proof;
    private List<ProofNodeCheckpoint> checkpoints;

    public ScriptController(ExecutorService executor, RuleApplicationListener listener) {
        this.view = new ScriptView(executor, this);
        this.listener = listener;

        view.caretPositionProperty().addListener(this::onCaretPositionChanged);
    }

    public void setProof(Proof proof) {
        this.proof = proof;

        this.checkpoints = ProofNodeCheckpointsBuilder.build(proof);

        view.replaceText(proof.getScript());
        view.getUndoManager().forgetHistory();
    }

    private void onCaretPositionChanged(Observable observable) {
        switchViewedNode();
    }

    private void switchViewedNode() {
        Position caretPosition = computePositionFromCharIdx(view.getCaretPosition(), view.getText());

        ProofNodeCheckpoint lastCheckpoint = checkpoints.get(0); // There should always be at least 1 checkpoint (the one at the start)

        // REVIEW Maybe stop iterating after finding checkpoints greater than the current position
        for (int i = 1; i < checkpoints.size(); i++) {
            ProofNodeCheckpoint checkpoint = checkpoints.get(i);
            if (caretPosition.compareTo(checkpoint.position) > 0) {
                lastCheckpoint = checkpoint;
            }
        }

        // If the selector points to nowhere, its probably because the rule closed the proof and didn't generate
        // another child...
        // REVIEW This is kind of ugly. In the future this off-by-one fix has to be removed
        if (!lastCheckpoint.selector.optionalGet(proof).isPresent()) {
            this.listener.onSwitchViewedNode(lastCheckpoint.selector.getParentSelector());
        }
        this.listener.onSwitchViewedNode(lastCheckpoint.selector);
    }

    private Position computePositionFromCharIdx(int charIdx, String text) {
        int line = 1;
        int charInLine = 0;
        for (int i = 0; i < charIdx; i++) {
            char c = text.charAt(i);

            if (c == '\n') {
                line++;
                charInLine = 0;
            } else {
                charInLine++;
            }
        }
        return new Position(line, charInLine);
    }

    @Override
    public void onScriptSave() {
        listener.onScriptSave();
    }

    @Override
    public void onAsyncScriptTextChanged(String text) {
        proof.setScriptTextAndInterpret(text);
        checkpoints = ProofNodeCheckpointsBuilder.build(proof);
        // TODO switchViewedNode();
    }

    public ScriptView getView() {
        return view;
    }
}
