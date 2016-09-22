package edu.kit.iti.algover.gui;

import edu.kit.iti.algover.model.CustomLeaf;
import edu.kit.iti.algover.model.ProjectTree;
import org.fife.ui.rsyntaxtextarea.RSyntaxTextArea;
import org.fife.ui.rsyntaxtextarea.SyntaxConstants;

import javax.swing.*;
import javax.swing.text.DefaultCaret;
import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.io.IOException;

/**
 * Will replace Rsyntaxtextarea in editorpanel when ready
 * Created by sarah on 9/12/16.
 */
public class DafnyEditor extends RSyntaxTextArea{

    GUICenter center;
    File fileToShow;
    public DafnyEditor(File filename, GUICenter center){
        this.center = center;
        this.fileToShow = filename;
        this.setSize(400,300);
        this.setSyntaxHighlighting();
        this.setCodeFoldingEnabled(true);
        this.setSrcText(fileToShow);

    }

    private void setSyntaxHighlighting() {
        //AbstractTokenMakerFactory atmf = (AbstractTokenMakerFactory) TokenMakerFactory.getDefaultInstance();
        //atmf.putMapping("text/Dafny", "edu.kit.iti.algover.gui.ANTLRTokenMaker");
        //this.setSyntaxEditingStyle("text/Dafny");

        this.setSyntaxEditingStyle(SyntaxConstants.SYNTAX_STYLE_JAVA);


    }

    public void setSrcText(File file){

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

            this.setText(text);

        } catch (IOException e) {
            JOptionPane.showMessageDialog(this.center.getMainwindow(),
                    "Unable to load file "+this.center.getLoadedDafnySrc(),
                    "File Loading",
                    JOptionPane.ERROR_MESSAGE);
            e.printStackTrace();


        }


    }
 //line
    public void setCaretPos(int lineNumber) {
        DefaultCaret caret = (DefaultCaret) getCaret();
        String[] lines = this.getText().split("\n");
        if(lineNumber == 0){
          this.setCaretPosition(0);
        }else {
            //int lineNumber;
//        if(selectedProjectSubTree.isLeaf()) {
//            CustomLeaf l = (CustomLeaf) selectedProjectSubTree;
//            lineNumber = l.getData().getRepresentation().getLine();

            int offset = 0;
            for (int i = 0; i < lineNumber; i++) {
                offset += lines[i].length() + 1;
            }
            this.setCaretPosition(offset - 1);
        }
//        }else{
//            setCaretPosition(0);
//        }
    }
}
