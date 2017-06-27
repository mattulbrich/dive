package edu.kit.iti.algover.editor;

import javafx.scene.control.Tab;
import javafx.scene.control.TabPane;
import org.fxmisc.richtext.CodeArea;

/**
 * Created by philipp on 26.06.17.
 */
public class EditorView extends TabPane {

    public EditorView() {
        Tab tab = new Tab();
        tab.setContent(new CodeArea("code area. yea"));
        getTabs().add(tab);
    }

}
