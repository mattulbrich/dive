package edu.kit.iti.algover.gui;

import edu.kit.iti.algover.gui.components.EditorScrollPane;
import edu.kit.iti.algover.gui.components.EditorTabbedPane;
import edu.kit.iti.algover.model.CustomLeaf;
import edu.kit.iti.algover.model.ProjectTree;
import edu.kit.iti.algover.util.FileUtil;
import org.fife.ui.rsyntaxtextarea.AbstractTokenMakerFactory;
import org.fife.ui.rsyntaxtextarea.RSyntaxTextArea;
import org.fife.ui.rsyntaxtextarea.SyntaxConstants;
import org.fife.ui.rsyntaxtextarea.TokenMakerFactory;
import org.fife.ui.rtextarea.RTextScrollPane;

import javax.swing.*;
import javax.swing.text.Caret;
import javax.swing.text.DefaultCaret;
import java.awt.*;
import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;
import java.io.*;

/**
 * EditorPanel consists of a tabbed pane, inside of which is a scroll pane containing an RSyntaxTextArea.
 *
 * Atm with JAVA highlighting
 * Created by sony on 07.09.2016.
 */

public class EditorPanel extends JPanel{

    EditorTabbedPane tabbedPane;
    //DafnyEditor textarea;
    RTextScrollPane sp;
    GUICenter center;
    RSyntaxTextArea textArea;

    public EditorPanel(GUICenter center)
    {
        this.center = center;
        this.setLayout(new BorderLayout());

        tabbedPane = new EditorTabbedPane(center);
        //textarea = new DafnyEditor();

        //textArea = new RSyntaxTextArea();
        //textArea.setSyntaxEditingStyle(SyntaxConstants.SYNTAX_STYLE_JAVA);

        //AbstractTokenMakerFactory atmf = (AbstractTokenMakerFactory) TokenMakerFactory.getDefaultInstance();
        //atmf.putMapping("text/Dafny", "edu.kit.iti.algover.gui.ANTLRTokenMaker");
        //textArea.setSyntaxEditingStyle("text/Dafny");

        //textArea.setCodeFoldingEnabled(true);
        //textArea.setSize(400,300);

        //DefaultCaret caret = (DefaultCaret)textArea.getCaret();
        //caret.setUpdatePolicy(DefaultCaret.ALWAYS_UPDATE);

        //sp = new RTextScrollPane(textArea);

        //tabbedPane.add(sp);

        add(tabbedPane, BorderLayout.CENTER);

        center.addPropertyChangeListener(new DafnySrcPropertyChangeListener(center));
    }




   /* public void setSrcText(File file){

        //System.out.println(file.toString());
        try {
        FileReader reader = new FileReader(file);
        BufferedReader r = new BufferedReader(reader);
        String str;
        String text = "";
            while ((str = r.readLine()) != null) {
                text += str+"\n";
            }
            r.close();

            this.textArea.setText(text);

        } catch (IOException e) {
            JOptionPane.showMessageDialog(this.center.getMainwindow(),
                    "Unable to load file "+this.center.getLoadedDafnySrc(),
                    "File Loading",
                    JOptionPane.ERROR_MESSAGE);
                        e.printStackTrace();


        }


    }*/


    private class DafnySrcPropertyChangeListener implements PropertyChangeListener {
        private final GUICenter center;

        public DafnySrcPropertyChangeListener(GUICenter center) {
            this.center = center;
        }

        @Override
        public void propertyChange(PropertyChangeEvent evt) {

            if (evt.getPropertyName() == GUICenter.PROJECT_DIR_CHANGED) {
                remove(tabbedPane);
                tabbedPane = new EditorTabbedPane(center);
                add(tabbedPane);

            }
            if (evt.getPropertyName() == GUICenter.DAFNY_SOURCE_CHANGED) {
                File loadedFile = center.getLoadedDafnySrc().getAbsoluteFile();
                tabbedPane.setTabInFocus(loadedFile);
           }
            if (evt.getPropertyName() == GUICenter.SUBTREE_SELECTION) {
                ProjectTree selectedProjectSubTree = center.getSelectedProjectSubTree();
                tabbedPane.setTabInFocus(selectedProjectSubTree.getFile());
                EditorScrollPane sp = tabbedPane.getTabWithName(selectedProjectSubTree.getFile().getAbsoluteFile().getName());
                sp.getEditor().setCaretPos(selectedProjectSubTree.getLineNumber());
            }
            if (evt.getPropertyName() == GUICenter.LEAF_TO_LOAD) {
                CustomLeaf selectedLeaf = center.getSelectedLeaf();
                tabbedPane.setTabInFocus(selectedLeaf.getFile());
                EditorScrollPane sp = tabbedPane.getTabWithName(selectedLeaf.getFile().getAbsoluteFile().getName());
                sp.getEditor().setCaretPos(selectedLeaf.getLineNumber());

            }
        }
    }
}
