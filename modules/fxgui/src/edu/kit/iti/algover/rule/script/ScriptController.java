/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.rule.script;

import de.jensd.fx.glyphs.fontawesome.utils.FontAwesomeIconFactory;
import de.jensd.fx.glyphs.materialdesignicons.MaterialDesignIcon;
import edu.kit.iti.algover.Lookup;
import edu.kit.iti.algover.MainController;
import edu.kit.iti.algover.editor.HighlightingRule;
import edu.kit.iti.algover.editor.LayeredHighlightingRule;
import edu.kit.iti.algover.proof.Proof;
import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.proof.ProofNodeSelector;
import edu.kit.iti.algover.referenceHighlighting.ReferenceHighlightingHandler;
import edu.kit.iti.algover.referenceHighlighting.ReferenceHighlightingObject;
import edu.kit.iti.algover.references.ProofTermReferenceTarget;
import edu.kit.iti.algover.references.ScriptReferenceTarget;
import edu.kit.iti.algover.rule.RuleApplicationListener;
import edu.kit.iti.algover.rules.RuleException;
import edu.kit.iti.algover.script.ast.ASTNode;
import edu.kit.iti.algover.script.ast.Position;
import edu.kit.iti.algover.script.ast.ProofScript;
import edu.kit.iti.algover.script.exceptions.ScriptCommandNotApplicableException;
import edu.kit.iti.algover.script.parser.Facade;
import edu.kit.iti.algover.script.parser.PrettyPrinter;
import edu.kit.iti.algover.util.ExceptionDetails;
import edu.kit.iti.algover.util.ExceptionDialog;
import edu.kit.iti.algover.util.RuleApp;
import javafx.beans.Observable;
import javafx.beans.property.SimpleIntegerProperty;
import javafx.beans.property.SimpleObjectProperty;
import javafx.beans.value.ChangeListener;
import javafx.beans.value.ObservableValue;
import javafx.collections.FXCollections;
import javafx.collections.ListChangeListener;
import javafx.collections.ObservableList;
import javafx.scene.control.MenuItem;
import javafx.scene.input.KeyCode;
import javafx.scene.input.KeyCodeCombination;
import javafx.scene.input.KeyCombination;
import javafx.scene.input.KeyEvent;
import org.antlr.v4.runtime.RecognitionException;
import org.antlr.v4.runtime.misc.ParseCancellationException;
import org.antlr.runtime.Token;
import org.fxmisc.richtext.model.StyleSpans;

import java.awt.*;
import java.io.StringWriter;
import java.time.Duration;
import java.util.*;
import java.util.List;
import java.util.concurrent.ExecutorService;
import java.util.function.Consumer;
import java.util.logging.Logger;
import java.util.prefs.PreferenceChangeEvent;
import java.util.prefs.PreferenceChangeListener;
import java.util.stream.Collectors;

/**
 * Controller for the ScriptArea. Contains methods to control the ScriptView.
 */
public class ScriptController implements ScriptViewListener, ReferenceHighlightingHandler {
    KeyCombination saveShortcut = new KeyCodeCombination(KeyCode.S, KeyCombination.CONTROL_DOWN);
    KeyCombination runShortcut = new KeyCodeCombination(KeyCode.R, KeyCombination.CONTROL_DOWN);
    KeyCombination reloadAndExecuteShortcut = new KeyCodeCombination(KeyCode.E, KeyCombination.CONTROL_DOWN);

    private final ScriptView view;
    private final RuleApplicationListener listener;
    private ProofNodeSelector selectedNode = new ProofNodeSelector();
    private Lookup lookup;

    private SimpleIntegerProperty fontSizeProperty = new SimpleIntegerProperty(12);

    //Is 1-Indexed!!
    private SimpleObjectProperty<Position> observableInsertPosition = new SimpleObjectProperty<Position>(new Position(1,0));


    private Proof proof;
    private ObservableList<ProofNodeCheckpoint> checkpoints = FXCollections.observableArrayList();

    private int sizeOfCheckpoints = 0;
    private LayeredHighlightingRulev4 highlightingRules;

    private PositionChangedListener positionListener;
    private CaretPositionChangedListener caretPositionListener;

    private MenuItem insertCasesItem;

    public ScriptController(ExecutorService executor, RuleApplicationListener listener, Lookup lookup) {
        this.view = new ScriptView(executor, this);
        this.view.setOnKeyReleased(this::handleShortcuts);
        this.listener = listener;
        this.highlightingRules = new LayeredHighlightingRulev4(2);
        this.lookup = lookup;

        this.insertCasesItem  = new MenuItem("Insert Cases", FontAwesomeIconFactory.get().createIcon(MaterialDesignIcon.CALL_SPLIT));

        lookup.register(this, ReferenceHighlightingHandler.class);

        this.fontSizeProperty.setValue(MainController.systemprefs.getInt("FONT_SIZE_SCRIPT_EDITOR", 12));

        MainController.systemprefs.addPreferenceChangeListener(new PreferenceChangeListener() {
            @Override
            public void preferenceChange(PreferenceChangeEvent preferenceChangeEvent) {
                int font_size_seq_view1 = preferenceChangeEvent.getNode().getInt("FONT_SIZE_SCRIPT_EDITOR", 12);
                fontSizeProperty.set(font_size_seq_view1);
            }
        });

        view.fontsizeProperty().bind(fontSizeProperty);


        view.setHighlightingRule(this.highlightingRules);
        caretPositionListener = new CaretPositionChangedListener(this);

        //  view.caretPositionProperty().addListener(this::onCaretPositionChanged);
        view.caretPositionProperty().addListener(caretPositionListener);

        //observable insertposition starts with 1
        observableInsertPosition.set(new Position(1,0));
        positionListener = new PositionChangedListener(this);

        observableInsertPosition.addListener(this.positionListener);


        view.getGutterAnnotations().get(0).setInsertMarker(true);
        view.getGutterAnnotations().get(0).setProofNode(new ProofNodeSelector());
        view.getGutterAnnotations().get(0).setProofNodeIsSelected(true);
        view.getGutterAnnotations().get(0).setProofNodeIsReferenced(true);
        view.requestLayout();
        view.getContextMenu().getItems().add(insertCasesItem);
        insertCasesItem.setOnAction(e -> onInsertCases());
        insertCasesItem.setDisable(true);

    }

    /**
     * sets the markers in the gutter. CAUTION: in contrast to visualization these markers start with index 0
     * @param old
     * @param nv
     */
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
        if(reloadAndExecuteShortcut.match(keyEvent)){
            listener.onScriptSave();
            runScript();
        }
        if (runShortcut.match(keyEvent)) {
            runScript();
        }
    }

    public void setProof(Proof proof) {
        this.proof = proof;

        this.checkpoints.setAll(ProofNodeCheckpointsBuilder.build(proof));

        view.replaceText(proof.getScript());
        view.getUndoManager().forgetHistory();
        runScript();
    }

    private void onCaretPositionChanged(Observable observable) {
       //this positions linenumber starts with 1
        Position caretPosition = computePositionFromCharIdx(view.getCaretPosition(), view.getText());
        createVisualSelectors(this.checkpoints);
        ProofNodeCheckpoint checkpoint = getCheckpointForPosition(caretPosition);
        if(checkpoint != null) {
            showSelectedSelector(checkpoint);
        }
        //updateInsertPosition();
        updateInsertPosition(observableInsertPosition.get());
        switchViewedNode();
        view.highlightLine();
    }

    /*private void updateInsertPosition() {
        Position caretPosition = computePositionFromCharIdx(view.getCaretPosition(), view.getText());
        ProofNodeCheckpoint insertCheckpoint = getCheckpointForPosition(caretPosition);
        if(insertCheckpoint != null) {
            setObservableInsertPosition(new Position(insertCheckpoint.position.getLineNumber() + 1, 0));
        } else {
            //no checkpoint found so the script should be empty
            setObservableInsertPosition((new Position (1, 0)));
        }
    }*/

    private void updateInsertPosition(Position oldInsertPos) {

        Position caretPosition = computePositionFromCharIdx(view.getCaretPosition(), view.getText());
        ProofNodeCheckpoint insertCheckpoint = getCheckpointForPosition(caretPosition);
        ProofNodeCheckpoint oldInsertCheckpoint = getCheckpointForPosition(oldInsertPos);

        int oldSize = this.sizeOfCheckpoints;
        int newSize = checkpoints.size();

        //no new checkpoints added -> we only moved cursor
        if(insertCheckpoint != null) {
            //no new checkpoints added -> we only moved cursor => set observableinsertPos to caretlinenumer+1
            if(oldSize == newSize) {
                //the position was probably changed by setting cursor somewhere else
                setObservableInsertPosition(new Position(insertCheckpoint.position.getLineNumber() + 1, 0));

            } else {
                //we have new checkpoints and need to find the position where to add the next command
                int difference = newSize - oldSize;
                assert difference >= 0;
                if(oldInsertCheckpoint != null)
                    setObservableInsertPosition(new Position( oldInsertPos.getLineNumber() + 1, 0));
                else
                    setObservableInsertPosition(new Position( insertCheckpoint.position.getLineNumber() + 1, 0));
            }
        } else {
            //no checkpoint found so the script should be empty
            setObservableInsertPosition((new Position (1, 0)));
        }

        this.sizeOfCheckpoints = checkpoints.size();


    }




    private void showSelectedSelector(ProofNodeCheckpoint checkpoint) {
        view.getGutterAnnotations().forEach(gutterAnnotation -> gutterAnnotation.setProofNodeIsSelected(false));
        view.getGutter().getLineAnnotation(checkpoint.position.getLineNumber()-1).setProofNodeIsSelected(true);
    }


    private void switchViewedNode() {
        //showSelectedSelector(checkpoint);
        //Position caretPosition = computePositionFromCharIdx(view.getCaretPosition(), view.getText());
        ProofNodeSelector pns = getNodeFromPosition(getObservableInsertPosition());
        if(pns != null) {
            this.listener.onSwitchViewedNode(pns);
            selectedNode = pns;
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
        ProofNodeCheckpoint ch = getCheckpointForPosition(pos);
        if(ch != null) {
            pn = proof.getProofNodeForAST(ch.node);
        }
        if(pn != null) {
            res = new ProofNodeSelector(pn);
        }
        return res;
    }

    private ProofNodeCheckpoint getNextCheckpointForPosition(Position pos) {

        List<ProofNodeCheckpoint> potCh = checkpoints.stream().filter(ch -> pos.compareTo(ch.position) < 0).collect(Collectors.toList());
        if (potCh.size() > 0) {
            return potCh.get(0);
        }
        return null;
    }

    private ProofNodeCheckpoint getCheckpointForPosition(Position pos) {
        List<ProofNodeCheckpoint> pCh = new ArrayList<>();
        for(ProofNodeCheckpoint ch: checkpoints){
            if(pos.compareTo(ch.position) > 0){
                pCh.add(ch);
            }
        }
        List<ProofNodeCheckpoint> potCh = checkpoints.stream().filter(ch -> pos.compareTo(ch.position) >= 0).collect(Collectors.toList());

        if(potCh.size() > 0) {
            return potCh.get(potCh.size() - 1);
        }
        return null;
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
        //rausfinden wer die Änderungen vorgenommen hat
        //gutter leeren
        //grauen
        //neuberechnen -> User
        //onCaretPositionChanged(null);

          view.setStyle("-fx-background-color: lightgray; -fx-font-size: "+fontSizeProperty.get()+"pt;");
          view.resetGutter();
          view.requestLayout();

    }

    /**
     * Interpret the proof script that is set in the current ScriptView
     */
    @Override
    public void runScript() {
        view.resetGutter();
        //view.requestLayout();

        Position oldInsertPos = getObservableInsertPosition();
        this.sizeOfCheckpoints = checkpoints.size();
        String text = view.getText();
        resetExceptionRendering();
        observableInsertPosition.removeListener(positionListener);
        view.caretPositionProperty().removeListener(caretPositionListener);
        Exception failException = null;


        try {
            //interpret the script
            ProofScript ps = Facade.getAST(text);

            PrettyPrinter pp = new PrettyPrinter();
            ps.accept(pp);

            view.replaceText(pp.toString());
            //System.out.println("pp.toString() = " + pp.toString());

            proof.setScriptTextAndInterpret(pp.toString());
        } catch (ParseCancellationException pce) {
            failException = pce;
        } catch (RecognitionException re) {
            failException = re;
         }
        if(failException == null) {
            failException = proof.getFailException();
        }

        checkpoints.setAll(ProofNodeCheckpointsBuilder.build(proof));
       // insertPosition = oldInsertPos;
        //observableInsertPosition.set(oldInsertPos);

        if(failException != null) {
            ExceptionDetails.ExceptionReportInfo eri = ExceptionDetails.extractReportInfo(failException);
            view.setHighlightedException(failException);
            renderException(eri);
            String message = failException.getMessage();
            if (message == null || message.isEmpty()) {
                message = failException.getClass() + " without message.";
            }
            Logger.getLogger(Logger.GLOBAL_LOGGER_NAME).severe(message);
            //failException.printStackTrace();
        } else {
            Logger.getGlobal().info("Successfully ran script.");
        }
        createVisualSelectors(checkpoints);
        observableInsertPosition.addListener(positionListener);
        view.caretPositionProperty().addListener(caretPositionListener);
        //new insert position has to be computed and updated
        //updateInsertPosition();
        updateInsertPosition(oldInsertPos);
        view.setStyle("-fx-background-color: white; -fx-font-size: "+fontSizeProperty.get()+"pt;");

        //JK: This should not be necessary since the changed text triggers onTextChanged and onCaretPositionChanged
        //SaG: this is necessary such that the right tab is shown in the view
        switchViewedNode();

    }


    public String onInsertCases() {
        try {
            //andRight on='|- _ && _';
            if(getNodeFromPosition(checkpoints.get(checkpoints.size()-1).position).get(proof).getParent().getChildren().size()>1){
                System.out.println("We are at branching");
            }
        } catch (RuleException e) {
            e.printStackTrace();
        }
        System.out.println("TODO insert cases");
        return "TODO";

    }

    /**
     * This method draws the circles in the gutter where a proof node can be selected
     * @param checkpoints
     */
    private void createVisualSelectors(List<ProofNodeCheckpoint> checkpoints) {
        if (checkpoints != null) {
            view.getGutterAnnotations().get(0).setProofNode(new ProofNodeSelector(proof.getProofRoot()));
            view.getGutterAnnotations().get(0).setProofNodeIsSelected(false);
        }

        for (ProofNodeCheckpoint checkpoint : this.checkpoints) {
            int checkpointline = checkpoint.position.getLineNumber();

            ProofNode pn = proof.getProofNodeForAST(checkpoint.node);
            if(pn == null) {
                continue;
            }
            ProofNodeSelector pns = new ProofNodeSelector(pn);
            if(checkpointline < view.getGutterAnnotations().size()) {
                view.getGutterAnnotations().get(checkpointline).setProofNode(pns);
                view.getGutterAnnotations().get(checkpointline).setProofNodeIsSelected(false);
            } else {
                GutterFactory gutterFactory = view.getGutter();
                GutterAnnotation lineAnnotation = gutterFactory.getLineAnnotation(checkpointline);
                lineAnnotation.setProofNode(pns);
                lineAnnotation.setProofNodeIsSelected(false);
            }

        }
//        view.requestLayout();
    }

    /**
     * Return the current ScriptView
     * @return
     */
    public ScriptView getView() {
        return view;
    }

    public void insertTextForSelectedNode(String text) {
        view.caretPositionProperty().removeListener(caretPositionListener);
        if(view.getText().equals("")) {
            view.insertText(0, text);
        } else {
            //updateInsertPosition();
            int insertAt = computeCharIdxFromPosition(observableInsertPosition.get(), view.getText());
            view.insertText(insertAt, text);
        }
        view.caretPositionProperty().addListener(caretPositionListener);
        //JK: Maybe this could be optimized if the prettyprinting is done here to avoid duplicated methods calls
        runScript();
    }

    private void renderException(ExceptionDetails.ExceptionReportInfo e) {
        highlightingRules.setLayer(0, new HighlightingRulev4() {
            ExceptionDetails.ExceptionReportInfo ri = e;
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
        view.updateHighlighting();
    }

    private void resetExceptionRendering() {
        highlightingRules.setLayer(0, (token, syntaxClasses) -> syntaxClasses);
    }

    /**
     * Set selected node such that observable insertposition changes. This method is needed if the tab selection changes
     * @param proofNode
     */
    public void setSelectedNode(ProofNodeSelector proofNode) {
        if(this.selectedNode != null && proofNode != null){
           if(!proofNode.equals(selectedNode)){
                if(checkpoints != null){
                   Map<ProofNodeSelector, Position> positionMap = new HashMap<>();
                   checkpoints.forEach(proofNodeCheckpoint
                           -> positionMap.put(getNodeFromPosition(proofNodeCheckpoint.position), proofNodeCheckpoint.position));
                   if(positionMap.get(proofNode)!= null){
                       setObservableInsertPosition(new Position(positionMap.get(proofNode).getLineNumber()+1, 0));
                       this.selectedNode = proofNode;
                   }
                }
           }
        }
    }

    /**
     * Return the Position, where the next proof command is added
     * @return Position
     */
    public Position getObservableInsertPosition() {
        return observableInsertPosition.get();
    }

    public SimpleObjectProperty<Position> observableInsertPositionProperty() {
        return observableInsertPosition;
    }

    public void setObservableInsertPosition(Position observableInsertPosition) {
        this.observableInsertPosition.set(observableInsertPosition);
    }

    /**
     * Mark all ProofNodes in the script that are referenced in the set of target passed as parameter
     * @param scriptReferenceTargetSet
     */
    public void viewReferences(Set<ScriptReferenceTarget> scriptReferenceTargetSet) {
        scriptReferenceTargetSet.stream().forEach(s -> {
            int linenumber = s.getLinenumber();
            view.getGutterAnnotations().get(linenumber-1).setProofNodeIsReferenced(true);
        });

    }

    @Override
    public void handleReferenceHighlighting(ReferenceHighlightingObject references) {
        removeReferenceHighlighting();
        Set<ScriptReferenceTarget> scriptReferenceTargetSet = references.getScriptReferenceTargetSet();
        viewReferences(scriptReferenceTargetSet);
    }

    @Override
    public void removeReferenceHighlighting() {
        view.getGutterAnnotations().forEach(gutterAnnotation -> {gutterAnnotation.setProofNodeIsReferenced(false);});
    }

    /**
     * Listener to act upon a change of the insertion position
     */
    private class PositionChangedListener implements ChangeListener<Position> {

        ScriptController sc ;
        public PositionChangedListener(ScriptController sc ){
            this.sc =sc;
        }


        @Override
        public void changed(ObservableValue<? extends Position> observable, Position oldValue, Position newValue) {
                this.sc.onInsertPositionChanged(oldValue, newValue);

        }
    }


    /**
     * Listener to act upon a change of the insertion position
     */
    private class CaretPositionChangedListener implements ChangeListener<Integer> {

        ScriptController sc ;
        public CaretPositionChangedListener(ScriptController sc ){
            this.sc =sc;
        }


        @Override
        public void changed(ObservableValue<? extends Integer> observable, Integer oldValue, Integer newValue) {
            this.sc.onCaretPositionChanged(observable);

        }
    }


}