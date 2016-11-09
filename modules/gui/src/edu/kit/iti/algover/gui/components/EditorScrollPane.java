package edu.kit.iti.algover.gui.components;

import org.fife.ui.rtextarea.RTextScrollPane;

/**
 * Created by sarah on 9/22/16.
 */
public class EditorScrollPane extends RTextScrollPane {
    DafnyEditor textarea;
    public EditorScrollPane(DafnyEditor textarea){
        super(textarea);
        this.textarea = textarea;
    }

    public DafnyEditor getEditor(){
        return this.textarea;
    }


}