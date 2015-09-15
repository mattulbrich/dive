package edu.kit.iti.algover.ui.gui;

import org.fxmisc.richtext.CodeArea;
import org.fxmisc.richtext.LineNumberFactory;

/**
 * Will be the class that bundles all specifics for Editor
 * Created by sarah on 9/15/15.
 */
public class Editor extends CodeArea {


    public Editor(){

        this.setParagraphGraphicFactory(LineNumberFactory.get(this));
        this.setMaxWidth(1000);


    }
}
