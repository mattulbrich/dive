package edu.kit.iti.algover.rule.script;

import edu.kit.iti.algover.proof.Proof;
import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.proof.ProofNodeSelector;
import edu.kit.iti.algover.rule.RuleApplicationListener;
import edu.kit.iti.algover.script.ast.ASTNode;
import edu.kit.iti.algover.script.ast.Position;
import edu.kit.iti.algover.script.ast.ProofScript;
import edu.kit.iti.algover.script.parser.Facade;
import edu.kit.iti.algover.script.parser.PrettyPrinter;
import edu.kit.iti.algover.util.ExceptionDetails;
import edu.kit.iti.algover.util.Pair;
import javafx.beans.Observable;
import javafx.beans.property.SimpleObjectProperty;
import javafx.scene.input.KeyCode;
import javafx.scene.input.KeyCodeCombination;
import javafx.scene.input.KeyCombination;
import javafx.scene.input.KeyEvent;

import java.awt.*;
import java.util.Collection;
import java.util.Collections;
import java.util.List;
import java.util.Map;
import java.util.concurrent.ExecutorService;
import java.util.logging.Logger;
import java.util.stream.Collectors;

public class ScriptController implements ScriptViewListener {
    KeyCombination saveShortcut = new KeyCodeCombination(KeyCode.S, KeyCombination.CONTROL_DOWN);

    private final ScriptView view;
    private final RuleApplicationListener listener;
    private ProofNode selectedNode = null;



    private SimpleObjectProperty<Position> observableInsertPosition = new SimpleObjectProperty<Position>(new Position(1,0));
    private Proof proof;
    private List<Pair<Position, ASTNode>> checkpoints;

    private LayeredHighlightingRulev4 highlightingRules;

    public ScriptController(ExecutorService executor, RuleApplicationListener listener) {
        this.view = new ScriptView(executor, this);
        this.view.setOnKeyReleased(this::handleShortcuts);
        this.listener = listener;
        this.highlightingRules = new LayeredHighlightingRulev4(2);
        view.setHighlightingRule(this.highlightingRules);

        view.caretPositionProperty().addListener(this::onCaretPositionChanged);

        observableInsertPosition.set(new Position(1,0));
        observableInsertPosition.addListener((o, old, nv) -> {
            onInsertPositionChanged(old, nv);
        });

        view.getGutterAnnotations().get(0).setInsertMarker(true);
        view.getGutterAnnotations().get(0).setProofNode(new ProofNodeSelector());
        view.getGutterAnnotations().get(0).setProofNodeIsSelected(true);

        view.requestLayout();

    }

    private void onInsertPositionChanged(Position old, Position nv) {
        if(old != null) {
            view.getGutterAnnotations().get(old.getLineNumber() - 1).setInsertMarker(false);
            view.getGutterAnnotations().forEach(gutterAnnotation -> gutterAnnotation.setProofNodeIsSelected(false));
            //view.getGutterAnnotations().get(old.getLineNumber() - 1).setProofNodeIsSelected(false);

        }
            if(view.getGutterAnnotations().size() > nv.getLineNumber()){
                view.getGutterAnnotations().get(nv.getLineNumber()-1).setInsertMarker(true);
                view.getGutterAnnotations().get(nv.getLineNumber()-1).setProofNodeIsSelected(true);

            } else {
                GutterAnnotation newlineAnnotation = view.getGutter().getLineAnnotation(nv.getLineNumber() - 1);
                newlineAnnotation.setInsertMarker(true);
                newlineAnnotation.setProofNodeIsSelected(true);
            }
        view.requestLayout();
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
        runScript();
    }

    private void onCaretPositionChanged(Observable observable) {
       //this positions linenumber starts with 1
        Position caretPosition = computePositionFromCharIdx(view.getCaretPosition(), view.getText());
        setObservableInsertPosition(caretPosition);
        this.checkpoints = ProofNodeCheckpointsBuilder.build(proof);
        //createVisualSelectors(this.checkpoints);
        //showSelectedSelector(checkpoint);
        switchViewedNode();
        view.highlightLine();
    }

    private void showSelectedSelector(ProofNodeCheckpoint checkpoint) {
        view.getGutterAnnotations().forEach(gutterAnnotation -> gutterAnnotation.setProofNodeIsSelected(false));
        view.getGutter().getLineAnnotation(checkpoint.caretPosition.getLineNumber()-1).setProofNodeIsSelected(true);
    }


    private void switchViewedNode() {
        //showSelectedSelector(checkpoint);
        ProofNodeSelector pns = getNodeFromPosition(getObservableInsertPosition());
        System.out.println("Switch to node: " + pns);
        if(pns != null) {
            this.listener.onSwitchViewedNode(pns);
        } else {
            System.out.println("cannot switch to node null");
        }
        view.requestLayout();
    }

    private ProofNodeSelector getNodeFromPosition(Position pos) {
        if(checkpoints.size() == 0) {
            return new ProofNodeSelector();
        }
        ProofNodeSelector res = new ProofNodeSelector();
        ProofNode pn = null;
        List<Pair<Position, ASTNode>> potCh = checkpoints.stream().filter(ch -> pos.compareTo(ch.fst) > 0).collect(Collectors.toList());
        if(potCh.size() > 0) {
            pn = proof.getProofNodeForAST(potCh.get(potCh.size() - 1).snd);
        }
        if(pn != null) {
            res = new ProofNodeSelector(pn);
        }
        return res;
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
        if(text == "") return 0;
        if(!text.contains("\n")) return text.length() - 1;
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
        System.out.println("ScriptController.onAsyncScriptTextChanged");
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
        view.setStyle("-fx-background-color: lightgray;");
        onCaretPositionChanged(null);
    }

    @Override
    public void runScript() {
        System.out.println("ScriptController.runScript");

        Position oldInsertPos = getObservableInsertPosition();
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
       // insertPosition = oldInsertPos;
        observableInsertPosition.set(oldInsertPos);
        //createVisualSelectors(checkpoints);

        switchViewedNode();
        view.setStyle("-fx-background-color: white;");
    }

    /*private void createVisualSelectors(List<ProofNodeCheckpoint> checkpoints) {
        for (ProofNodeCheckpoint checkpoint : this.checkpoints) {
            int checkpointline = checkpoint.position.getLineNumber();

            if(checkpointline < view.getGutterAnnotations().size()) {
                view.getGutterAnnotations().get(checkpointline).setProofNode(checkpoint.selector);
                view.getGutterAnnotations().get(checkpointline).setProofNodeIsSelected(false);
            } else {
                GutterFactory gutterFactory = view.getGutter();
                GutterAnnotation lineAnnotation = gutterFactory.getLineAnnotation(checkpointline);
                lineAnnotation.setProofNode(checkpoint.selector);
                lineAnnotation.setProofNodeIsSelected(false);
            }

        }
//        view.requestLayout();
    }*/

    public ScriptView getView() {
        return view;
    }

    public void insertTextForSelectedNode(String text) {
        if(view.getText().equals("")) {
            view.insertText(0, text);
        } else {
            int insertAt = computeCharIdxFromPosition(observableInsertPosition.get(), view.getText());
            view.insertText(insertAt, text);
        }
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

    public void setSelectedNode(ProofNodeSelector proofNode) {
        if(!proofNode.equals(selectedNode)) {
//            selectedNode = proofNode;
            if (checkpoints != null) {
//                List<ProofNodeCheckpoint> potCheckpoints = checkpoints.stream().filter(ch -> ch.selector.equals(proofNodeSelector)).collect(Collectors.toList());
//                if (potCheckpoints.size() > 0) {
//                    Position insertPosition = potCheckpoints.get(potCheckpoints.size() - 1).caretPosition;
//                    observableInsertPosition.set(insertPosition);
//                    //switchViewedNode();
//                }
            }
        }
    }

    public Position getObservableInsertPosition() {
        return observableInsertPosition.get();
    }

    public SimpleObjectProperty<Position> observableInsertPositionProperty() {
        return observableInsertPosition;
    }

    public void setObservableInsertPosition(Position observableInsertPosition) {
        this.observableInsertPosition.set(observableInsertPosition);
    }

}