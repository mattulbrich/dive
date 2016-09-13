package edu.kit.iti.algover.gui;

import org.fife.ui.rsyntaxtextarea.AbstractTokenMakerFactory;
import org.fife.ui.rsyntaxtextarea.RSyntaxTextArea;
import org.fife.ui.rsyntaxtextarea.TokenMakerFactory;
import org.fife.ui.rtextarea.RTextScrollPane;

import javax.swing.*;
import java.awt.*;

/**
 * EditorPanel consists of a tabbed pane, inside of which is a scroll pane containing an RSyntaxTextArea.
 *
 * Created by sony on 07.09.2016.
 */

public class EditorPanel extends JPanel{

    JTabbedPane tabbedPane;
    DafnyEditor textarea;
    RTextScrollPane sp;

    public EditorPanel()
    {
        this.setLayout(new BorderLayout());

        tabbedPane = new JTabbedPane();
        //textarea = new DafnyEditor();
        RSyntaxTextArea textArea = new RSyntaxTextArea();
        AbstractTokenMakerFactory atmf = (AbstractTokenMakerFactory) TokenMakerFactory.getDefaultInstance();
        //this.setSyntaxEditingStyle(SyntaxConstants.SYNTAX_STYLE_JAVA);

        atmf.putMapping("text/Dafny", "edu.kit.iti.algover.gui.ANTLRTokenMaker");

        textArea.setSyntaxEditingStyle("text/Dafny");
        textArea.setCodeFoldingEnabled(true);
        textArea.setSize(200,300);

        sp = new RTextScrollPane(textArea);
        tabbedPane.add(sp);

        add(tabbedPane, BorderLayout.CENTER);
    }
}
