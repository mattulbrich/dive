package edu.kit.iti.algover.rule.script;

import edu.kit.iti.algover.proof.Proof;
import edu.kit.iti.algover.proof.ProofNodeSelector;
import edu.kit.iti.algover.rule.RuleApplicationListener;
import edu.kit.iti.algover.script.ast.Position;
import edu.kit.iti.algover.script.ast.ProofScript;
import edu.kit.iti.algover.util.RuleApp;
import javafx.beans.Observable;
import javafx.concurrent.Task;
import javafx.scene.input.KeyCode;
import javafx.scene.input.KeyCodeCombination;
import javafx.scene.input.KeyCombination;
import javafx.scene.input.KeyEvent;
import org.fxmisc.richtext.model.StyleSpans;

import java.time.Duration;
import java.util.Collection;
import java.util.List;
import java.util.Optional;
import java.util.concurrent.ExecutorService;
import java.util.function.Consumer;

public class ScriptController implements ScriptViewListener {
    KeyCombination saveShortcut = new KeyCodeCombination(KeyCode.S, KeyCombination.CONTROL_DOWN);

    private final ScriptView view;
    private final RuleApplicationListener listener;

    private Proof proof;
    private List<ProofNodeCheckpoint> checkpoints;

    public ScriptController(ExecutorService executor, RuleApplicationListener listener) {
        this.view = new ScriptView(executor, this);
        this.view.setOnKeyReleased(this::handleShortcuts);
        this.listener = listener;

        view.caretPositionProperty().addListener(this::onCaretPositionChanged);
    }

    private void handleShortcuts(KeyEvent keyEvent) {
        if (saveShortcut.match(keyEvent)) {
            listener.onScriptSave();
        }
    }

    public void setProof(Proof proof) {
        this.proof = proof;

        this.checkpoints = ProofNodeCheckpointsBuilder.build(proof);

        view.replaceText(proof.getScript());
        view.getUndoManager().forgetHistory();
    }

    private void onCaretPositionChanged(Observable observable) {
        switchViewedNode();
        view.highlightLine();
    }


    private void switchViewedNode() {
        Position caretPosition = computePositionFromCharIdx(view.getCaretPosition(), view.getText());

        ProofNodeCheckpoint checkpoint = getCheckpointForCaretPosition(caretPosition);

        // If the selector points to nowhere, its probably because the rule closed the proof and didn't generate
        // another child...
        // REVIEW This is kind of ugly. In the future this off-by-one fix has to be removed
        if (!checkpoint.selector.optionalGet(proof).isPresent()) {
            this.listener.onSwitchViewedNode(checkpoint.selector.getParentSelector());
        }

        this.listener.onSwitchViewedNode(checkpoint.selector);
    }

    private ProofNodeCheckpoint getCheckpointForCaretPosition(Position caretPosition) {
        ProofNodeCheckpoint lastCheckpoint = checkpoints.get(0); // There should always be at least 1 checkpoint (the one at the start)
        // REVIEW Maybe stop iterating after finding checkpoints greater than the current position
        for (int i = 1; i < checkpoints.size(); i++) {
            ProofNodeCheckpoint checkpoint = checkpoints.get(i);
            if (caretPosition.compareTo(checkpoint.position) > 0) {
                lastCheckpoint = checkpoint;
            }
        }

        return lastCheckpoint;
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

    private int computeCharIdxFromPosition(Position position, String text) {
        int charIdx = 0;
        for (int i = 0; i < position.getLineNumber() - 1; ++i) {
            charIdx += text.substring(0, text.indexOf('\n')).length() + 1;
            text = text.substring(text.indexOf('\n') + 1);
        }
        return charIdx + position.getCharInLine();
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

    public void insertTextForSelectedNode(String text) {
        Position caretPosition = computePositionFromCharIdx(view.getCaretPosition(), view.getText());
        ProofNodeCheckpoint checkpoint = getCheckpointForCaretPosition(caretPosition);
        int insertAt = computeCharIdxFromPosition(checkpoint.caretPosition, view.getText());
        view.insertText(insertAt, text);
    }
}
