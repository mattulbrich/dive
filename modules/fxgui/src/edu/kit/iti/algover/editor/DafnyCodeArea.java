package edu.kit.iti.algover.editor;

import de.jensd.fx.glyphs.GlyphsDude;
import de.jensd.fx.glyphs.fontawesome.FontAwesomeIcon;
import edu.kit.iti.algover.AlgoVerApplication;
import edu.kit.iti.algover.MainController;
import edu.kit.iti.algover.parser.DafnyLexer;
import edu.kit.iti.algover.util.AsyncHighlightingCodeArea;
import javafx.application.Platform;
import javafx.beans.property.BooleanProperty;
import javafx.beans.property.SimpleBooleanProperty;
import javafx.beans.value.ChangeListener;
import javafx.beans.value.ObservableValue;
import javafx.concurrent.Task;
import javafx.scene.control.ContextMenu;
import javafx.scene.control.MenuItem;
import javafx.scene.input.KeyCode;
import javafx.scene.input.KeyCombination;
import org.antlr.runtime.ANTLRStringStream;
import org.antlr.runtime.Token;
import org.fxmisc.richtext.LineNumberFactory;
import org.fxmisc.richtext.model.StyleSpans;
import org.fxmisc.richtext.model.StyleSpansBuilder;
import org.fxmisc.wellbehaved.event.EventPattern;
import org.fxmisc.wellbehaved.event.InputMap;
import org.fxmisc.wellbehaved.event.Nodes;

import java.util.Collection;
import java.util.Collections;
import java.util.concurrent.ExecutorService;

/**
 * Shows a dafny-syntax-highlighted code editor.
 * <p>
 * Syntax highlighting is done asynchronously using an {@link ExecutorService}.
 * <p>
 * Additional highlighting on top is configurable via {@link #setHighlightingRule(HighlightingRule)}.
 * <p>
 * Created by philipp on 28.06.17.
 */
public class DafnyCodeArea extends AsyncHighlightingCodeArea {

    private HighlightingRule highlightingRule;
    private final ExecutorService executor;
    private BooleanProperty textChangedProperty;
    private String currentProofText;
    private DafnyCodeAreaListener listener;


    /**
     * @param text     the initial code inside the code editor
     * @param executor the executor service to be used for asynchronously
     *                 calculating syntax highlighting (that is: running the parser,
     *                 computing style spans)
     */
    public DafnyCodeArea(String text, ExecutorService executor, DafnyCodeAreaListener listener) {
        super(executor);
        this.highlightingRule = (token, syntaxClasses) -> syntaxClasses;
        this.executor = executor;
        this.listener = listener;
        getStylesheets().add(AlgoVerApplication.class.getResource("syntax-highlighting.css").toExternalForm());
        setParagraphGraphicFactory(LineNumberFactory.get(this));

        textChangedProperty = new SimpleBooleanProperty(true);

        currentProofText = text;
        //font size and shortcuts
        int font_size_editor = MainController.systemprefs.getInt("FONT_SIZE_EDITOR", 12);
        setStyle("-fx-font-size: "+font_size_editor+";");
        registerShortcuts();


        textProperty().addListener(new ChangeListener<String>() {
            @Override
            public void changed(ObservableValue<? extends String> observable, String oldValue, String newValue) {
                rerenderHighlighting();
                if (textIsSimilar(currentProofText, newValue)) {
                    textChangedProperty.setValue(false);
                } else {
                    textChangedProperty.setValue(true);
                }
            }
        });
        replaceText(text);
        getUndoManager().forgetHistory();

        initContextMenu();
    }

    private void registerShortcuts() {
        Nodes.addInputMap(this, InputMap.consume(
                EventPattern.keyPressed(KeyCode.PLUS,KeyCombination.CONTROL_DOWN), event -> {
                    int font_size_editor = MainController.systemprefs.getInt("FONT_SIZE_EDITOR", 12);
                    font_size_editor++;
                    updateFontSize(font_size_editor);
                }));

        Nodes.addInputMap(this, InputMap.consume(
                EventPattern.keyPressed(KeyCode.MINUS,KeyCombination.CONTROL_DOWN), event -> {
                    int font_size_editor = MainController.systemprefs.getInt("FONT_SIZE_EDITOR", 12);
                    font_size_editor--;
                    updateFontSize(font_size_editor);
                }));
    }

    private void updateFontSize(int font_size_editor) {
        setStyle("-fx-font-size: "+font_size_editor+";");
        MainController.systemprefs.putInt("FONT_SIZE_EDITOR", font_size_editor);

    }

    private void initContextMenu() {
        MenuItem save = new MenuItem("Save dafny file", GlyphsDude.createIcon(FontAwesomeIcon.SAVE));
        MenuItem saveAll = new MenuItem("Save all dafny files", GlyphsDude.createIcon(FontAwesomeIcon.SAVE));

        save.setOnAction(event -> listener.saveSelectedFile());
        saveAll.setOnAction(event -> listener.saveAllFiles());

        ContextMenu menu = new ContextMenu(
                save,
                saveAll
        );
        setContextMenu(menu);
    }

    public void updateProofText() {
        currentProofText = getText();
        textChangedProperty.setValue(false);
    }

    private boolean textIsSimilar(String s1, String s2) {
        s1 = s1.replaceAll("\\s*", " ");
        s2 = s2.replaceAll("\\s*", " ");
        return s1.equals(s2);
    }

    /**
     * Toggles a re-rendering of the syntax highlighting. Call this method
     * if you exchanged the additionally configurable {@link HighlightingRule},
     * i.e. after a call to {@link #setHighlightingRule(HighlightingRule)}.
     */
    public void rerenderHighlighting() {
        Task<StyleSpans<Collection<String>>> task = runAsyncHighlightingTask();
        task.setOnSucceeded(event -> {
            final StyleSpans<Collection<String>> styleSpans = task.getValue();
            Platform.runLater(() -> applyHighlighting(styleSpans));
        });
    }

    @Override
    protected StyleSpans<Collection<String>> computeHighlighting(String text) {
        StyleSpansBuilder<Collection<String>> builder = new StyleSpansBuilder<>();

        if (text.isEmpty()) {
            builder.add(Collections.emptyList(), 0);
            return builder.create();
        }

        DafnyLexer lexer = new DafnyLexer(new ANTLRStringStream(text));

        Token token;
        while ((token = lexer.nextToken()).getType() != Token.EOF) {
            builder.add(
                    highlightingRule.handleToken(
                            token,
                            styleClassForToken(token.getType())),
                    token.getText().length());
        }

        return builder.create();
    }

    private Collection<String> styleClassForToken(int type) {
        switch (type) {
            case DafnyLexer.METHOD:
            case DafnyLexer.CLASS:
            case DafnyLexer.VAR:
            case DafnyLexer.IF:
            case DafnyLexer.THEN:
            case DafnyLexer.ELSE:
            case DafnyLexer.RETURNS:
            case DafnyLexer.WHILE:
            case DafnyLexer.FUNCTION:
            case DafnyLexer.ASSIGN:
            case DafnyLexer.RETURN:
            case DafnyLexer.INCLUDE:
                return Collections.singletonList("code-keyword");
            case DafnyLexer.REQUIRES:
            case DafnyLexer.ENSURES:
            case DafnyLexer.INVARIANT:
            case DafnyLexer.DECREASES:
            case DafnyLexer.ASSERT:
            case DafnyLexer.MODIFIES:
            case DafnyLexer.LEMMA:
            case DafnyLexer.SETTINGS:
            case DafnyLexer.OLD:
            case DafnyLexer.EX:
            case DafnyLexer.ALL:
            case DafnyLexer.LABEL:
                return Collections.singleton("specification-keyword");
            case DafnyLexer.MULTILINE_COMMENT:
            case DafnyLexer.SINGLELINE_COMMENT:
            case DafnyLexer.ALGOVER_COMMENT:
                return Collections.singleton("comment");
            case DafnyLexer.INT:
            case DafnyLexer.BOOL:
            case DafnyLexer.SEQ:
            case DafnyLexer.SET:
            case DafnyLexer.ARRAY:
                return Collections.singleton("type-literal");
            case DafnyLexer.INT_LIT:
            case DafnyLexer.TRUE:
            case DafnyLexer.FALSE:
            case DafnyLexer.STRING_LIT:
                return Collections.singleton("value-literal");
            default:
                return Collections.emptyList();
        }
    }

    public HighlightingRule getHighlightingRule() {
        return highlightingRule;
    }

    /**
     * Set another highlighting rule. This rule will compute additional highlighting and has
     * the lexers computed highlighting classes information available.
     *
     * @param highlightingRule the highlighting rule to execute on top of the dafny syntax highlighting
     * @see HighlightingRule
     */
    public void setHighlightingRule(HighlightingRule highlightingRule) {
        if (highlightingRule == null) {
            this.highlightingRule = (token, syntaxClasses) -> syntaxClasses;
        } else {
            this.highlightingRule = highlightingRule;
        }
    }

    public BooleanProperty getTextChangedProperty() {
        return textChangedProperty;
    }

    public boolean getTextChanged() {
        return textChangedProperty.get();
    }

    public void setTextChanged(boolean value) {
        textChangedProperty.setValue(value);
    }


}
