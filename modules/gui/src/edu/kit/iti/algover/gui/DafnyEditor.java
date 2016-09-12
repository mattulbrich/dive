package edu.kit.iti.algover.gui;

import org.fife.ui.rsyntaxtextarea.AbstractTokenMakerFactory;
import org.fife.ui.rsyntaxtextarea.RSyntaxTextArea;
import org.fife.ui.rsyntaxtextarea.SyntaxConstants;
import org.fife.ui.rsyntaxtextarea.TokenMakerFactory;

/**
 * Created by sarah on 9/12/16.
 */
public class DafnyEditor extends RSyntaxTextArea{

    public DafnyEditor(){
       this.setSize(20, 60);
        this.setSyntaxHighlighting();


    }

    private void setSyntaxHighlighting() {
        AbstractTokenMakerFactory atmf = (AbstractTokenMakerFactory) TokenMakerFactory.getDefaultInstance();
        //this.setSyntaxEditingStyle(SyntaxConstants.SYNTAX_STYLE_JAVA);

        atmf.putMapping("text/Dafny", "ANTLRTokenMaker");
        this.setSyntaxEditingStyle("text/Dafny");
        this.setCodeFoldingEnabled(true);
    }
}
