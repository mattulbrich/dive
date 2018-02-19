package edu.kit.iti.algover.rule.script;

import edu.kit.iti.algover.proof.Proof;
import edu.kit.iti.algover.proof.ProofNodeSelector;
import edu.kit.iti.algover.script.ast.Position;
import javafx.beans.Observable;

import java.util.List;
import java.util.function.Consumer;

public class ScriptController {

    private final ScriptView view;
    private final Consumer<ProofNodeSelector> onSwitchViewedNode;

    private Proof proof;
    private List<ProofNodeCheckpoint> checkpoints;

    public ScriptController(ScriptView view, Consumer<ProofNodeSelector> onSwitchViewedNode) {
        this.view = view;
        this.onSwitchViewedNode = onSwitchViewedNode;

        view.caretPositionProperty().addListener(this::onCaretPositionChanged);
    }

    public void setProof(Proof proof) {
        this.proof = proof;

        this.checkpoints = ProofNodeCheckpointsBuilder.build(proof);

        view.clear();
        view.insertText(0, proof.getScript());
    }

    private void onCaretPositionChanged(Observable observable) {
        Position caretPosition = computePositionFromCharIdx(view.getCaretPosition(), view.getText());

        ProofNodeCheckpoint lastCheckpoint = checkpoints.get(0); // There should always be at least 1 checkpoint (the one at the start)

        // REVIEW Maybe stop iterating after finding checkpoints greater than the current position
        for (int i = 1; i < checkpoints.size(); i++) {
            ProofNodeCheckpoint checkpoint = checkpoints.get(i);
            if (caretPosition.compareTo(checkpoint.position) > 0) {
                lastCheckpoint = checkpoint;
            }
        }

        onSwitchViewedNode.accept(lastCheckpoint.selector);
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
}
