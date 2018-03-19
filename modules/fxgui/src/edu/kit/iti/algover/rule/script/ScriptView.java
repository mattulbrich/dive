package edu.kit.iti.algover.rule.script;

import de.jensd.fx.glyphs.GlyphsDude;
import de.jensd.fx.glyphs.fontawesome.FontAwesomeIcon;
import edu.kit.iti.algover.AlgoVerApplication;
import edu.kit.iti.algover.script.ScriptLanguageLexer;
import edu.kit.iti.algover.script.parser.Facade;
import edu.kit.iti.algover.util.AsyncHighlightingCodeArea;
import javafx.scene.control.ContextMenu;
import javafx.scene.control.MenuItem;
import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.Token;
import org.fxmisc.richtext.model.StyleSpans;
import org.fxmisc.richtext.model.StyleSpansBuilder;

import java.io.ByteArrayInputStream;
import java.io.InputStream;
import java.nio.charset.StandardCharsets;
import java.util.Collection;
import java.util.Collections;
import java.util.concurrent.ExecutorService;

/**
 * Created by Philipp on 24.07.2017.
 */
public class ScriptView extends AsyncHighlightingCodeArea {

    private final ScriptViewListener listener;

    public ScriptView(ExecutorService executor, ScriptViewListener listener) {
        super(executor);
        this.listener = listener;

        getStylesheets().add(AlgoVerApplication.class.getResource("syntax-highlighting.css").toExternalForm());

        MenuItem save = new MenuItem("Save Proof Script", GlyphsDude.createIcon(FontAwesomeIcon.SAVE));

        save.setOnAction(event -> this.listener.onScriptSave());

        ContextMenu menu = new ContextMenu(
                save
        );
        setContextMenu(menu);
        setupAsyncSyntaxhighlighting();
    }

    @Override
    protected StyleSpans<Collection<String>> computeHighlighting(String text) throws Exception {
        StyleSpansBuilder<Collection<String>> builder = new StyleSpansBuilder<>();

        if (text.isEmpty()) {
            builder.add(Collections.emptyList(), 0);
            return builder.create();
        }

        InputStream stream = new ByteArrayInputStream(text.getBytes(StandardCharsets.UTF_8));
        ScriptLanguageLexer lexer = new ScriptLanguageLexer(CharStreams.fromStream(stream, StandardCharsets.UTF_8));

        Token token;
        while ((token = lexer.nextToken()).getType() != Token.EOF) {
            builder.add(styleClassForToken(token.getType()),
                    token.getText().length());
        }

        lexer.reset();

        listener.onAsyncScriptTextChanged(text);

        return builder.create();
    }

    private Collection<String> styleClassForToken(int type) {
        switch (type) {
            case ScriptLanguageLexer.TERM_LITERAL:
                return Collections.singleton("value-literal");
            case ScriptLanguageLexer.SINGLE_LINE_COMMENT:
            case ScriptLanguageLexer.MULTI_LINE_COMMENT:
                return Collections.singleton("comment");
            default:
                return Collections.emptyList();
        }
    }

}