package edu.kit.iti.algover.rule.script;

import edu.kit.iti.algover.editor.HighlightingRule;
import edu.kit.iti.algover.editor.LayeredHighlightingRule;
import edu.kit.iti.algover.proof.Proof;
import edu.kit.iti.algover.proof.ProofNodeSelector;
import edu.kit.iti.algover.rule.RuleApplicationListener;
import edu.kit.iti.algover.script.ast.Position;
import edu.kit.iti.algover.script.ast.ProofScript;
import edu.kit.iti.algover.script.exceptions.ScriptCommandNotApplicableException;
import edu.kit.iti.algover.script.parser.Facade;
import edu.kit.iti.algover.script.parser.PrettyPrinter;
import edu.kit.iti.algover.util.ExceptionDetails;
import edu.kit.iti.algover.util.RuleApp;
import javafx.beans.Observable;
import javafx.concurrent.Task;
import javafx.scene.input.KeyCode;
import javafx.scene.input.KeyCodeCombination;
import javafx.scene.input.KeyCombination;
import javafx.scene.input.KeyEvent;
import org.antlr.runtime.Token;
import org.fxmisc.richtext.model.StyleSpans;

import java.io.StringWriter;
import java.time.Duration;
import java.util.Collection;
import java.util.Collections;
import java.util.List;
import java.util.Optional;
import java.util.concurrent.ExecutorService;
import java.util.function.Consumer;
import java.util.logging.Logger;
import java.util.stream.Collectors;

public class ScriptController implements ScriptViewListener {
    KeyCombination saveShortcut = new KeyCodeCombination(KeyCode.S, KeyCombination.CONTROL_DOWN);

    private final ScriptView view;
    private final RuleApplicationListener listener;
    private ProofNodeSelector selectedNode = null;
    Position insertPosition = new Position(0, 0);

    private Proof proof;
    private List<ProofNodeCheckpoint> checkpoints;

    private LayeredHighlightingRulev4 highlightingRules;

    public ScriptController(ExecutorService executor, RuleApplicationListener listener) {
        this.view = new ScriptView(executor, this);
        this.view.setOnKeyReleased(this::handleShortcuts);
        this.listener = listener;
        this.highlightingRules = new LayeredHighlightingRulev4(2);
        view.setHighlightingRule(this.highlightingRules);

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
        Position caretPosition = computePositionFromCharIdx(view.getCaretPosition(), view.getText());
        ProofNodeCheckpoint checkpoint = getCheckpointForCaretPosition(caretPosition);
        insertPosition = checkpoint.caretPosition;
        this.checkpoints = ProofNodeCheckpointsBuilder.build(proof);
        switchViewedNode();
        view.highlightLine();
    }


    private void switchViewedNode() {
        Position caretPosition = insertPosition;

        ProofNodeCheckpoint checkpoint = getCheckpointForCaretPosition(caretPosition);

        // If the selector points to nowhere, its probably because the rule closed the proof and didn't generate
        // another child...
        // REVIEW This is kind of ugly. In the future this off-by-one fix has to be removed
        if (!checkpoint.selector.optionalGet(proof).isPresent()) {
            if(checkpoint.selector.getParentSelector() != null) {
                this.listener.onSwitchViewedNode(checkpoint.selector.getParentSelector());
            } else {
                this.listener.onSwitchViewedNode(checkpoint.selector);
            }
        }

        this.listener.onSwitchViewedNode(checkpoint.selector);
    }

    private ProofNodeCheckpoint getCheckpointForCaretPosition(Position caretPosition) {
        ProofNodeCheckpoint lastCheckpoint = checkpoints.get(0); // There should always be at least 1 checkpoint (the one at the start)
        // REVIEW Maybe stop iterating after finding checkpoints greater than the current position
        for (int i = 1; i < checkpoints.size(); i++) {
            ProofNodeCheckpoint checkpoint = checkpoints.get(i);
            if (caretPosition.compareTo(checkpoint.position) >= 0) {
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
        /*resetExceptionRendering();

        ProofScript ps = Facade.getAST(text);
        PrettyPrinter pp = new PrettyPrinter();
        ps.accept(pp);

        view.replaceText(pp.toString());
        //System.out.println("pp.toString() = " + pp.toString());

        proof.setScriptTextAndInterpret(pp.toString());

        if(proof.getFailException() != null) {
            renderException(proof.getFailException());
            Logger.getLogger(Logger.GLOBAL_LOGGER_NAME).severe(proof.getFailException().getMessage());
        }*/
        //checkpoints = ProofNodeCheckpointsBuilder.build(proof);
        // TODO switchViewedNode();
        onCaretPositionChanged(null);
    }

    @Override
    public void runScript() {
        Position oldInsertPos = insertPosition;
        String text = view.getText();
        resetExceptionRendering();

        ProofScript ps = Facade.getAST(text);
        PrettyPrinter pp = new PrettyPrinter();
        ps.accept(pp);

        view.replaceText(pp.toString());
        //System.out.println("pp.toString() = " + pp.toString());

        proof.setScriptTextAndInterpret(pp.toString());

        if(proof.getFailException() != null) {
            renderException(proof.getFailException());
            Logger.getLogger(Logger.GLOBAL_LOGGER_NAME).severe(proof.getFailException().getMessage());
            proof.getFailException().printStackTrace();
        }
        checkpoints = ProofNodeCheckpointsBuilder.build(proof);
        insertPosition = oldInsertPos;
        switchViewedNode();
    }

    public ScriptView getView() {
        return view;
    }

    public void insertTextForSelectedNode(String text) {
        int insertAt = computeCharIdxFromPosition(insertPosition, view.getText());
        view.insertText(insertAt, text);
        runScript();
    }

    private void renderException(Exception e) {
        highlightingRules.setLayer(0, new HighlightingRulev4() {
            ExceptionDetails.ExceptionReportInfo ri = ExceptionDetails.extractReportInfo(e);
            int line = ri.getLine();

            @Override
            public Collection<String> handleToken(org.antlr.v4.runtime.Token token, Collection<String> syntaxClasses) {
                int tokenLine = token.getLine();
                if (tokenLine == line) {
                    return Collections.singleton("error");
                }
                return syntaxClasses;
            }
        });
    }

    private void resetExceptionRendering() {
        highlightingRules.setLayer(0, (token, syntaxClasses) -> syntaxClasses);
    }

    public void setSelectedNode(ProofNodeSelector proofNodeSelector) {
        if(!proofNodeSelector.equals(selectedNode)) {
            selectedNode = proofNodeSelector;
            if (checkpoints != null) {
                List<ProofNodeCheckpoint> potCheckpoints = checkpoints.stream().filter(ch -> ch.selector.equals(proofNodeSelector)).collect(Collectors.toList());
                if (potCheckpoints.size() > 0) {
                    insertPosition = potCheckpoints.get(potCheckpoints.size() - 1).caretPosition;
                    //switchViewedNode();
                }
            }
        }
    }
}