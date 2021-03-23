/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.rule.script;

import de.jensd.fx.glyphs.fontawesome.FontAwesomeIcon;
import de.jensd.fx.glyphs.fontawesome.utils.FontAwesomeIconFactory;
import de.jensd.fx.glyphs.materialdesignicons.MaterialDesignIcon;
import edu.kit.iti.algover.AlgoVerApplication;
import edu.kit.iti.algover.PropertyManager;
import edu.kit.iti.algover.editor.HighlightingRule;
import edu.kit.iti.algover.nuscript.parser.ScriptLexer;
import edu.kit.iti.algover.proof.Proof;
import edu.kit.iti.algover.util.AsyncHighlightingCodeArea;
import edu.kit.iti.algover.util.ExceptionDetails;
import javafx.beans.property.SimpleIntegerProperty;
import javafx.collections.ObservableList;
import javafx.scene.control.ContextMenu;
import javafx.scene.control.MenuItem;
import javafx.scene.control.Tooltip;
import javafx.scene.input.MouseEvent;
import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.Token;
import org.fxmisc.richtext.CharacterHit;
import org.fxmisc.richtext.model.StyleSpans;
import org.fxmisc.richtext.model.StyleSpansBuilder;

import java.io.ByteArrayInputStream;
import java.io.InputStream;
import java.nio.charset.StandardCharsets;
import java.util.Collection;
import java.util.Collections;
import java.util.OptionalInt;
import java.util.concurrent.ExecutorService;

/**
 * Created by Philipp on 24.07.2017.
 * Renamed from ScriptView to ScriptCodeView by Valentin on 20.10.2020
 */
public class ScriptCodeView extends AsyncHighlightingCodeArea {


    private final ScriptViewListener listener;
    private HighlightingRulev4 highlightingRule;
    private Exception highlightedException = null;
    private ExceptionDetails.ExceptionReportInfo highlightedExceptionInfo = null;
    private final Tooltip tooltip = new Tooltip("");

    public int getFontsize() {
        return fontsize.get();
    }

    public SimpleIntegerProperty fontsizeProperty() {
        return fontsize;
    }

    public void setFontsize(int fontsize) {
        this.fontsize.set(fontsize);
    }

    private SimpleIntegerProperty fontsize = new SimpleIntegerProperty(12);

    public GutterFactory getGutter() {
        return gutter;
    }

    private GutterFactory gutter;

    public ScriptCodeView(ExecutorService executor, ScriptViewListener listener) {
        super(executor);
        this.listener = listener;
        this.highlightingRule = (token, syntaxClasses) -> syntaxClasses;

        setStyle("-fx-font-size: "+fontsizeProperty().get()+"pt;");

        getStylesheets().add(AlgoVerApplication.class.getResource("syntax-highlighting.css").toExternalForm());
        setContextMenu(null);

        //set gutter factory for checkpoints
        gutter = new GutterFactory(this, fontsizeProperty());
        this.setParagraphGraphicFactory(gutter);
        

        setupAsyncSyntaxhighlighting();

        setOnMouseMoved(this::handleHover);

        fontsizeProperty().addListener((observable, oldValue, newValue) -> {
            setStyle("-fx-font-size: "+fontsizeProperty().get()+"pt;");
            requestLayout();
        });
        /*this.caretPositionProperty().addListener((observable, oldValue, newValue) -> {
            System.out.println("oldValue = " + oldValue);
            System.out.println("newValue = " + newValue);
        });*/

    }


    public void resetGutter(){
      //  gutter.getAnnotations().setAll(new SimpleListProperty<>(FXCollections.observableArrayList()));
        gutter = new GutterFactory(this, fontsizeProperty());
        this.setParagraphGraphicFactory(gutter);
    }

    @Override
    protected StyleSpans<Collection<String>> computeHighlighting(String text) throws Exception {
        StyleSpansBuilder<Collection<String>> builder = new StyleSpansBuilder<>();

        if (text.isEmpty()) {
            builder.add(Collections.emptyList(), 0);
            return builder.create();
        }

        InputStream stream = new ByteArrayInputStream(text.getBytes(StandardCharsets.UTF_8));
        ScriptLexer lexer = new ScriptLexer(CharStreams.fromStream(stream, StandardCharsets.UTF_8));

        Token token;
        while ((token = lexer.nextToken()).getType() != org.antlr.runtime.Token.EOF) {
            builder.add(
                    highlightingRule.handleToken(
                            token,
                            styleClassForToken(token.getType())),
                    token.getText().length());
        }

        //listener.onAsyncScriptTextChanged(text);

        return builder.create();
    }

    private Collection<String> styleClassForToken(int type) {
        switch (type) {
            case ScriptLexer.TERM_LITERAL:
                return Collections.singleton("value-literal");
            case ScriptLexer.SINGLE_LINE_COMMENT:
            case ScriptLexer.MULTI_LINE_COMMENT:
                return Collections.singleton("comment");
            case ScriptLexer.STRING_LITERAL:
                return Collections.singleton("value-literal");
            case ScriptLexer.SELECTOR_LITERAL:
                return Collections.singleton("value-literal");
            default:
                return Collections.emptyList();
        }
    }

    public void updateHighlighting() {
        try {
            applyHighlighting(computeHighlighting(getText()));
        } catch (Exception e) {
            System.out.println("Error updating highlight.");
        }
    }

    /**
     * Set another highlighting rule. This rule will compute additional highlighting and has
     * the lexers computed highlighting classes information available.
     *
     * @param highlightingRule the highlighting rule to execute on top of the dafny syntax highlighting
     * @see HighlightingRule
     */
    public void setHighlightingRule(HighlightingRulev4 highlightingRule) {
        if (highlightingRule == null) {
            this.highlightingRule = (token, syntaxClasses) -> syntaxClasses;
        } else {
            this.highlightingRule = highlightingRule;
        }
    }

    public void highlightLine() {
        StyleSpansBuilder<Collection<String>> builder = new StyleSpansBuilder<>();
        String text = getText();

        ScriptLexer lexer = null;
        try {
            InputStream stream = new ByteArrayInputStream(text.getBytes(StandardCharsets.UTF_8));
            lexer = new ScriptLexer(CharStreams.fromStream(stream, StandardCharsets.UTF_8));
        } catch (Exception e) {
            System.out.println("could not render new highlighting.");
        }

        if (lexer != null) {
            Token token;
            while ((token = lexer.nextToken()).getType() != Token.EOF) {
//                if (token.getLine() == getCurrentParagraph() + 1) {
//                    Collection<String> sytle = new ArrayList<>(styleClassForToken(token.getType()));
//                    sytle.add("highlight-line");
//                    builder.add(sytle,
//                            token.getText().length());
//                } else {
                    builder.add(styleClassForToken(token.getType()),
                            token.getText().length());
//                }
            }
            try {
                builder.create();
                applyHighlighting(builder.create());
            } catch (IllegalStateException e) {
                //This shouldnt be a problem since it only singles that there are no spans
            }

        }
    }


    private void handleHover(MouseEvent mouseEvent) {
        CharacterHit hit = hit(mouseEvent.getX(), mouseEvent.getY());
        System.out.println("Char hit");
        OptionalInt charIdx = hit.getCharacterIndex();
        if(charIdx.isPresent() && highlightedException != null) {
            edu.kit.iti.algover.nuscript.Position moPos = computePositionFromCharIdx(charIdx.getAsInt(), getText());
            if(moPos.getLineNumber() == highlightedExceptionInfo.getLine()) {
                tooltip.setText(highlightedExceptionInfo.getMessage());
                Tooltip.install(this, tooltip);

            }
        } else {
            Tooltip.uninstall(this, tooltip);
        }
    }

    private edu.kit.iti.algover.nuscript.Position computePositionFromCharIdx(int charIdx, String text) {
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
        return new edu.kit.iti.algover.nuscript.Position(line, charInLine);
    }

    public void setHighlightedException(Exception e) {
        this.highlightedException = e;
        highlightedExceptionInfo = ExceptionDetails.extractReportInfo(highlightedException);
        String[] lines = getText().split("\n");
        int start = 0;
        for (int i = 0; i < highlightedExceptionInfo.getLine() - 1; i++) {
            start += lines[i].length();
            start += 1;
        }
        selectRange(start, start + lines[highlightedExceptionInfo.getLine() - 1].length());

    }
    public ObservableList<GutterAnnotation> getGutterAnnotations() {
        return gutter.getAnnotations();
    }


}
