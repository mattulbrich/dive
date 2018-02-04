package edu.kit.iti.algover.rule;

import edu.kit.iti.algover.proof.Proof;
import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.proof.ProofNodeSelector;
import edu.kit.iti.algover.script.ast.ASTNode;
import edu.kit.iti.algover.script.ast.Position;
import javafx.scene.input.MouseEvent;
import org.fxmisc.richtext.CharacterHit;

public class ScriptController {

    private final ScriptView view;

    private Proof proof;

    public ScriptController(ScriptView view) {
        this.view = view;

        view.setOnMouseClicked(this::mouseClicked);
    }

    private void mouseClicked(MouseEvent mouseEvent) {
        CharacterHit hit = view.hit(mouseEvent.getX(), mouseEvent.getY());
        hit.getCharacterIndex().ifPresent(charIdx -> {
            QueryScriptByPositionVisitor visitor = new QueryScriptByPositionVisitor(computePositionFromCharIdx(charIdx, view.getText()));
            ASTNode foundNode = visitor.visit(proof.getScript());
            ProofNodeSelector selector = findSelectorPointingTo(new ProofNodeSelector(), proof.getProofRoot(), foundNode);
            System.out.println(selector);
        });
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
