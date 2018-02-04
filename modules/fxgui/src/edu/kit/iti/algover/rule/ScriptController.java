package edu.kit.iti.algover.rule;

import edu.kit.iti.algover.proof.Proof;
import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.proof.ProofNodeSelector;
import edu.kit.iti.algover.script.ast.ASTNode;
import edu.kit.iti.algover.script.ast.CallStatement;
import edu.kit.iti.algover.script.ast.Position;
import javafx.scene.input.MouseEvent;
import org.fxmisc.richtext.CharacterHit;

import java.util.function.Consumer;

public class ScriptController {

    private final ScriptView view;
    private final Consumer<ProofNodeSelector> onSwitchViewedNode;

    private Proof proof;

    public ScriptController(ScriptView view, Consumer<ProofNodeSelector> onSwitchViewedNode) {
        this.view = view;
        this.onSwitchViewedNode = onSwitchViewedNode;

        view.setOnMouseClicked(this::mouseClicked);
    }

    private void mouseClicked(MouseEvent mouseEvent) {
        CharacterHit hit = view.hit(mouseEvent.getX(), mouseEvent.getY());
        hit.getCharacterIndex().ifPresent(charIdx -> {
            Position position = computePositionFromCharIdx(charIdx, view.getText());
            QueryScriptByPositionVisitor visitor = new QueryScriptByPositionVisitor(position);
            ASTNode foundNode = visitor.visit(proof.getScript());

            if (foundNode != null) {
                ProofNodeSelector selector = findSelectorPointingTo(new ProofNodeSelector(), proof.getProofRoot(), foundNode);
                // TODO: I don't like that you have to click on the text specifically!
                // Ideally I should put a listener on the caret position (but only on click I guess?)
                if (foundNode instanceof CallStatement &&
                        acrossHalf(foundNode.getStartPosition(), foundNode.getEndPosition(), position)) {
                    selector = new ProofNodeSelector(selector, 0);
                }
                System.out.println(selector);
                onSwitchViewedNode.accept(selector);
            }
        });
    }

    private boolean acrossHalf(Position startPosition, Position endPosition, Position position) {
        if (startPosition.getLineNumber() == endPosition.getLineNumber()) {
            return position.getCharInLine() > (startPosition.getCharInLine() + endPosition.getCharInLine()) / 2;
        }
        return position.getLineNumber() > (startPosition.getLineNumber() + endPosition.getLineNumber()) / 2;
    }

    private ProofNodeSelector findSelectorPointingTo(ProofNodeSelector pathSoFar, ProofNode proofNode, ASTNode node) {
        if (proofNode.getMutator().contains(node)) {
            return pathSoFar;
        } else {
            for (int i = 0; i < proofNode.getChildren().size(); i++) {
                ProofNode child = proofNode.getChildren().get(i);
                ProofNodeSelector subselector = findSelectorPointingTo(new ProofNodeSelector(pathSoFar, i), child, node);
                if (subselector != null) {
                    return subselector;
                }
            }
            return null;
        }
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

    public void setProof(Proof proof) {
        this.proof = proof;
    }
}
