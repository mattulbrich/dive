package edu.kit.iti.algover.gui;

import edu.kit.iti.algover.model.CustomLeaf;
import edu.kit.iti.algover.model.ProjectTree;
import edu.kit.iti.algover.util.FileUtil;
import org.fife.ui.rsyntaxtextarea.AbstractTokenMakerFactory;
import org.fife.ui.rsyntaxtextarea.RSyntaxTextArea;
import org.fife.ui.rsyntaxtextarea.SyntaxConstants;
import org.fife.ui.rsyntaxtextarea.TokenMakerFactory;
import org.fife.ui.rtextarea.RTextScrollPane;

import javax.swing.*;
import java.awt.*;
import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;
import java.io.*;

/**
 * EditorPanel consists of a tabbed pane, inside of which is a scroll pane containing an RSyntaxTextArea.
 *
 * Created by sony on 07.09.2016.
 */

public class EditorPanel extends JPanel{

    JTabbedPane tabbedPane;
    //DafnyEditor textarea;
    RTextScrollPane sp;
    GUICenter center;
    RSyntaxTextArea textArea;

    public EditorPanel(GUICenter center)
    {
        this.center = center;
        this.setLayout(new BorderLayout());

        tabbedPane = new JTabbedPane();
        //textarea = new DafnyEditor();
        textArea = new RSyntaxTextArea();
        AbstractTokenMakerFactory atmf = (AbstractTokenMakerFactory) TokenMakerFactory.getDefaultInstance();
        //textArea.setSyntaxEditingStyle(SyntaxConstants.SYNTAX_STYLE_JAVA);

        atmf.putMapping("text/Dafny", "edu.kit.iti.algover.gui.ANTLRTokenMaker");

        textArea.setSyntaxEditingStyle("text/Dafny");
        textArea.setCodeFoldingEnabled(true);
        textArea.setSize(400,300);

        sp = new RTextScrollPane(textArea);

        tabbedPane.add(sp);

        add(tabbedPane, BorderLayout.CENTER);

        center.addPropertyChangeListener(new DafnySrcPropertyChangeListener(center));
    }

    private void setCaretPosition(ProjectTree selectedProjectSubTree) {
        System.out.println(textArea.getText().length());

        String[] lines =textArea.getText().split("\n");
        System.out.println("ArrayLength "+lines.length);

        int lineNumber;
        if(selectedProjectSubTree instanceof CustomLeaf){
            CustomLeaf l = (CustomLeaf) selectedProjectSubTree;
            lineNumber = l.getData().getRepresentation().getLine();
        }else{
           lineNumber = 0;
        }
        int offset = 0;
        for(int i = 0; i< lineNumber; i++){
            offset += lines[i].length();
        }
        System.out.println("Position "+offset);
        //System.out.println(lineNumber);
        textArea.setCaretPosition(offset);
    }


    public void setSrcText(File file){
        System.out.println(file.toString());
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


    }


    private class DafnySrcPropertyChangeListener implements PropertyChangeListener {
        private final GUICenter center;

        public DafnySrcPropertyChangeListener(GUICenter center) {
            this.center = center;
        }

        @Override
        public void propertyChange(PropertyChangeEvent evt) {
            if(evt.getPropertyName() == GUICenter.DAFNY_SOURCE_CHANGED || evt.getPropertyName() == GUICenter.TREE_SELECTION){
                try {
                    setSrcText(center.getLoadedDafnySrc().getAbsoluteFile());
                    setCaretPosition(center.getSelectedProjectSubTree());

                } catch (Exception e) {
                JOptionPane.showMessageDialog(center.getMainwindow(),
                "Unable to load file "+ center.getLoadedDafnySrc(),
                "Source File Loading",
                JOptionPane.ERROR_MESSAGE);
                    e.printStackTrace();

                }
            }
        }
    }
}
