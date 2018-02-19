package edu.kit.iti.algover.rule.script;

import de.jensd.fx.glyphs.GlyphsDude;
import de.jensd.fx.glyphs.fontawesome.FontAwesomeIcon;
import javafx.scene.control.ContextMenu;
import javafx.scene.control.MenuItem;
import org.fxmisc.richtext.CodeArea;

/**
 * Created by Philipp on 24.07.2017.
 */
public class ScriptView extends CodeArea {
    // TODO: Syntax highlighting

    private ScriptViewListener listener;

    public ScriptView() {
        MenuItem save = new MenuItem("Save Proof Script", GlyphsDude.createIcon(FontAwesomeIcon.SAVE));

        save.setOnAction(event -> this.listener.onScriptSave());

        ContextMenu menu = new ContextMenu(
                save
        );
        setContextMenu(menu);
    }

    public void setListener(ScriptViewListener listener) {
        this.listener = listener;
    }
}
