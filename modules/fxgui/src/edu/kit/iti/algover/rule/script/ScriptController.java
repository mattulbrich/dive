/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.rule.script;

import edu.kit.iti.algover.Lookup;
import edu.kit.iti.algover.MainController;
import edu.kit.iti.algover.PropertyManager;
import edu.kit.iti.algover.proof.Proof;
import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.proof.ProofNodeSelector;
import edu.kit.iti.algover.proof.ProofStatus;
import edu.kit.iti.algover.referenceHighlighting.ReferenceHighlightingHandler;
import edu.kit.iti.algover.referenceHighlighting.ReferenceHighlightingObject;
import edu.kit.iti.algover.references.ScriptReferenceTarget;
import edu.kit.iti.algover.rule.RuleApplicationListener;
import edu.kit.iti.algover.script.ast.*;
import edu.kit.iti.algover.script.parser.Facade;
import edu.kit.iti.algover.script.parser.PrettyPrinter;
import edu.kit.iti.algover.settings.ProjectSettings;
import edu.kit.iti.algover.util.ExceptionDetails;
import javafx.beans.Observable;
import javafx.beans.property.SimpleBooleanProperty;
import javafx.beans.property.SimpleIntegerProperty;
import javafx.beans.property.SimpleObjectProperty;
import javafx.geometry.Pos;
import javafx.scene.control.Alert;
import javafx.scene.control.ButtonType;
import javafx.scene.input.KeyCode;
import javafx.scene.input.KeyCodeCombination;
import javafx.scene.input.KeyCombination;
import javafx.scene.input.KeyEvent;
import org.antlr.v4.runtime.RecognitionException;
import org.antlr.v4.runtime.misc.ParseCancellationException;

import java.util.*;
import java.util.List;
import java.util.concurrent.ExecutorService;
import java.util.logging.Logger;
import java.util.stream.Collectors;

/**
 * Controller for the ScriptArea. Contains methods to control the ScriptView.
 */
public class ScriptController implements ScriptViewListener, ReferenceHighlightingHandler {
    KeyCombination saveShortcut = new KeyCodeCombination(KeyCode.S, KeyCombination.CONTROL_DOWN);
    KeyCombination runShortcut = new KeyCodeCombination(KeyCode.R, KeyCombination.CONTROL_DOWN);
    KeyCombination insertCasesShortcut = new KeyCodeCombination(KeyCode.I, KeyCombination.CONTROL_DOWN);
    KeyCombination reloadAndExecuteShortcut = new KeyCodeCombination(KeyCode.E, KeyCombination.CONTROL_DOWN);

    private final ScriptView view;
    private final RuleApplicationListener listener;
    private ProofNodeSelector selectedNode = null;
    private Lookup lookup;

    private SimpleIntegerProperty fontSizeProperty = new SimpleIntegerProperty(12);
    private SimpleBooleanProperty scriptChanged = new SimpleBooleanProperty(false);


    /**
     * The insert position where the next command is inserted
     */
    private SimpleObjectProperty<Position> observableInsertPosition = new SimpleObjectProperty<Position>(new Position(1, 0), "Observable Insert Position");
    private List<ProofNodeCheckpoint> checkpoints;

    private LayeredHighlightingRulev4 highlightingRules;

    public ScriptController(ExecutorService executor, RuleApplicationListener listener, Lookup lookup) {
        this.view = new ScriptView(executor, this);
        this.view.setOnKeyReleased(this::handleShortcuts);
        this.listener = listener;
        this.highlightingRules = new LayeredHighlightingRulev4(2);
        this.lookup = lookup;

        lookup.register(this, ReferenceHighlightingHandler.class);

        this.fontSizeProperty.setValue(MainController.systemprefs.getInt("FONT_SIZE_SCRIPT_EDITOR", 12));


        MainController.systemprefs.addPreferenceChangeListener(preferenceChangeEvent -> {
            int font_size_seq_view1 = preferenceChangeEvent.getNode().getInt("FONT_SIZE_SCRIPT_EDITOR", 12);
            fontSizeProperty.set(font_size_seq_view1);
        });

        view.fontsizeProperty().bind(fontSizeProperty);

        PropertyManager.getInstance().currentProofNodeSelector.addListener(((observable, oldValue, newValue) -> {
            if (newValue != null) {
                this.setSelectedNode(newValue);
            }
        }));
        PropertyManager.getInstance().currentProofStatus.addListener(((observable, oldValue, newValue) -> {
            if(newValue == ProofStatus.CHANGED_SCRIPT) {
                view.setStyle("-fx-background-color: #c4c1c9; -fx-font-size: "+fontSizeProperty.get()+"pt;");
            } else if(newValue == ProofStatus.CLOSED) {
                view.setStyle("-fx-background-color: #cefaae; -fx-font-size: "+fontSizeProperty.get()+"pt;");
            } else {
                view.setStyle("-fx-background-color: white; -fx-font-size: "+fontSizeProperty.get()+"pt;");
            }
        }));
        PropertyManager.getInstance().currentProof.addListener(((observable, oldValue, newValue) -> setProof(newValue)));

        this.scriptChanged.addListener(((observable, oldValue, newValue) -> {
            if(newValue) {
                PropertyManager.getInstance().currentProofStatus.set(ProofStatus.CHANGED_SCRIPT);
            }
        }));

        view.setHighlightingRule(this.highlightingRules);

        view.caretPositionProperty().addListener(this::onCaretPositionChanged);

        observableInsertPosition.set(new Position(1,0));
        observableInsertPosition.addListener((o, old, nv) -> onInsertPositionChanged(old, nv));

        view.getGutterAnnotations().get(0).setInsertMarker(true);
        view.getGutterAnnotations().get(0).setProofNode(new ProofNodeSelector());
        view.getGutterAnnotations().get(0).setProofNodeIsSelected(true);
        view.getGutterAnnotations().get(0).setProofNodeIsReferenced(true);

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
        if(reloadAndExecuteShortcut.match(keyEvent)){
            listener.onScriptSave();
            runScript();
        }
        if (runShortcut.match(keyEvent)) {
            runScript();
        }
        if (insertCasesShortcut.match(keyEvent)) {
            onInsertCases();
        }
    }

    private void setProof(Proof proof) {
        if(proof != null) {
            this.checkpoints = ProofNodeCheckpointsBuilder.build(proof);

            view.replaceText(proof.getScript());
            view.getUndoManager().forgetHistory();
            runScript();
        }
    }

    private void onCaretPositionChanged(Observable observable) {
       //this positions linenumber starts with 1
        Position caretPosition = computePositionFromCharIdx(view.getCaretPosition(), view.getText());
        ProofNodeCheckpoint checkpoint = getCheckpointForCaretPosition(caretPosition);
        //insertPosition = checkpoint.caretPosition;
        observableInsertPosition.set(checkpoint.caretPosition);
        this.checkpoints = ProofNodeCheckpointsBuilder.build(PropertyManager.getInstance().currentProof.get());
        createVisualSelectors(this.checkpoints);
        //showSelectedSelector(checkpoint);
        switchViewedNode();
        view.highlightLine();
    }

    private void showSelectedSelector(ProofNodeCheckpoint checkpoint) {
        view.getGutterAnnotations().forEach(gutterAnnotation -> gutterAnnotation.setProofNodeIsSelected(false));
        view.getGutter().getLineAnnotation(checkpoint.caretPosition.getLineNumber()-1).setProofNodeIsSelected(true);
    }


    private void switchViewedNode() {
        Position caretPosition = getObservableInsertPosition();

        ProofNodeCheckpoint checkpoint = getCheckpointForCaretPosition(caretPosition);

        // If the selector points to nowhere, its probably because the rule closed the proof and didn't generate
        // another child...
        // REVIEW This is kind of ugly. In the future this off-by-one fix has to be removed
        if (checkpoint.selector.optionalGet(PropertyManager.getInstance().currentProof.get()).isEmpty()) {
            if(checkpoint.selector.getParentSelector() != null) {
                PropertyManager.getInstance().currentProofNodeSelector.set(checkpoint.selector.getParentSelector());
            } else {
                PropertyManager.getInstance().currentProofNodeSelector.set(checkpoint.selector);
            }
        } else {
            PropertyManager.getInstance().currentProofNodeSelector.set(checkpoint.selector);
        }
        showSelectedSelector(checkpoint);
        view.requestLayout();

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
        if(text.equals("")) return 0;
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
        resetExceptionRendering();

        /*ProofScript ps = Facade.getAST(text);
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

          scriptChanged.set(true);
          view.resetGutter();
          view.requestLayout();

    }

    /**
     * Interpret the proof script that is set in the current ScriptView
     */
    @Override
    public void runScript() {
        view.resetGutter();
        view.requestLayout();

        Position oldInsertPos = getObservableInsertPosition();
        String text = view.getText();
        resetExceptionRendering();

        Exception failException = null;
        try {
            ProofScript ps = Facade.getAST(text);
            PrettyPrinter pp = new PrettyPrinter();
            ps.accept(pp);

            view.replaceText(pp.toString());
            //System.out.println("pp.toString() = " + pp.toString());
        /*ProofScript ps = Facade.getAST(text);

        PrettyPrinter pp = new PrettyPrinter();
        ps.accept(pp);
        view.replaceText(pp.toString());

        proof.setScriptTextAndInterpret(pp.toString());*/
            PropertyManager.getInstance().currentProof.get().setScriptTextAndInterpret(text);
        } catch (ParseCancellationException | RecognitionException pce) {
            failException = pce;
        }
        if(failException == null) {
            failException = PropertyManager.getInstance().currentProof.get().getFailException();
        }


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
        checkpoints = ProofNodeCheckpointsBuilder.build(PropertyManager.getInstance().currentProof.get());
       // insertPosition = oldInsertPos;
        observableInsertPosition.set(oldInsertPos);
        createVisualSelectors(checkpoints);

        PropertyManager.getInstance().currentProofStatus.set(PropertyManager.getInstance().currentProof.get().getProofStatus());
        switchViewedNode();
        scriptChanged.set(false);
    }

    @Override
    public void onInsertCases() {
        if(scriptChanged.get()) {
            Alert alert = new Alert(Alert.AlertType.CONFIRMATION,
        "Do you want to run the script now?");
            alert.setTitle("Run script.");
            alert.setHeaderText("In order to insert missing case statements the script has to be run first.");
            alert.showAndWait();
            if(alert.getResult() == ButtonType.OK) {
                runScript();
            } else {
                return;
            }
        }
        ProofScript script = PropertyManager.getInstance().currentProof.get().getProofScript();
        Statements newScript = insertCasesForStatement(PropertyManager.getInstance().currentProof.get().getProofRoot(), script.getBody());
        script.setBody(newScript);
        PrettyPrinter pp = new PrettyPrinter();
        script.accept(pp);
        view.replaceText(pp.toString());
        runScript();
    }

    /**@
     * recursivly inserts all missing case statements in the given script
     *
     * @param pn the proofnode for which the cases should be inserted
     * @param stmts the current script that should be extended by the missing case statements
     * @return a new script containing all necessary case statements
     */
    private Statements insertCasesForStatement(ProofNode pn, Statements stmts) {
        if(stmts.size() == 0) {
            return stmts;
        }
        Statements result = new Statements();
        for (int i = 0; i < stmts.size() - 1; ++i) {
            if(stmts.get(i) instanceof CallStatement) {
                result.add(stmts.get(i));
            } else {
                Logger.getGlobal().warning("Only the last statement may be a cases-statement.");
                return stmts;
            }
            if((pn.getChildren() != null && pn.getChildren().size() == 1)) {
                    pn = pn.getChildren().get(0);
            } else if (stmts.size() - 2 != i) {
                Logger.getGlobal().warning("Script has unexpected number of children at some point.");
                return stmts;
            }
        }
        Statement st = stmts.get(stmts.size() - 1);
        if(pn.getChildren().size() == 1 && st instanceof CallStatement) {
            result.add(st);
        } else if (pn.getChildren().size() > 1 && st instanceof CasesStatement) {
                result.add(createCasesForNode(pn, ((CasesStatement) st).getCases()));
        } else if (pn.getChildren().size() > 1 && !(st instanceof CasesStatement)) {
            result.add(st);
            result.add(createCasesForNode(pn));
        }

        return result;
    }

    /**@
     * Creates all cases for the given proofnode except the ones given in cases
     *
     * @param pn the proofnode for which the cases should be created
     * @param cases the cases that already exist
     * @return a case statement containing all necesarry cases
     */
    private Statement createCasesForNode(ProofNode pn, List<CaseStatement> cases) {
        CasesStatement res = new CasesStatement();
        for(ProofNode p : pn.getChildren()) {
            boolean found = false;
            for(CaseStatement caze : cases) {
                if(!(caze instanceof SimpleCaseStatement)) {
                    throw new UnsupportedOperationException("Creating cases for non simple Casestatements currently " +
                            "not supported.");
                }
                SimpleCaseStatement scs = (SimpleCaseStatement)caze;
                //apparently some guards are string literals and some are MathcExpressions...
                if(scs.getGuard() instanceof StringLiteral) {
                    String caseString = scs.getGuard().getText();
                    caseString = caseString.replaceAll("\"", "");
                    if (caseString.equals(p.getLabel())) {
                        Statements statements = insertCasesForStatement(p, scs.getBody());
                        scs.setBody(statements);
                        res.getCases().add(scs);
                        found = true;
                    }
                } else if (scs.getGuard() instanceof MatchExpression) {
                    Expression pattern =  ((MatchExpression) scs.getGuard()).getPattern();
                    String caseString = pattern.getText();
                    caseString = caseString.replaceAll("\"", "");
                    if(caseString.equals(p.getLabel())) {
                        Statements statements = insertCasesForStatement(p, scs.getBody());
                        scs.setBody(statements);
                        res.getCases().add(scs);
                        found = true;
                    }
                }
            }
            if(!found) {
                SimpleCaseStatement c = new SimpleCaseStatement();
                c.setGuard(new StringLiteral(p.getLabel()));
                c.setBody(new Statements());
                res.getCases().add(c);
            }
        }
        return res;
    }

    private Statement createCasesForNode(ProofNode pn) {
        return createCasesForNode(pn, new ArrayList<>());
    }

    /**
     * Create the annotations for the ScriptGutterView according to the checkpointslist
     * @param checkpoints
     */
    private void createVisualSelectors(List<ProofNodeCheckpoint> checkpoints) {
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
    }

    /**
     * Return the current ScriptView
     * @return
     */
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
     * Set the selected proof node in the ScriptView
     * @param proofNodeSelector the selector for the proofNode to be selected
     */
    public void setSelectedNode(ProofNodeSelector proofNodeSelector) {
        if(!proofNodeSelector.equals(selectedNode)) {
            selectedNode = proofNodeSelector;
            if (checkpoints != null) {
                List<ProofNodeCheckpoint> potCheckpoints = checkpoints.stream().filter(ch -> ch.selector.equals(proofNodeSelector)).collect(Collectors.toList());
                if (potCheckpoints.size() > 0) {
                    Position insertPosition = potCheckpoints.get(potCheckpoints.size() - 1).caretPosition;
                    observableInsertPosition.set(insertPosition);
                    //switchViewedNode();
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
        view.getGutterAnnotations().forEach(gutterAnnotation -> gutterAnnotation.setProofNodeIsReferenced(false));
    }
}