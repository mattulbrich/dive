package edu.kit.iti.algover.Actions;

import edu.kit.iti.algover.gui.DafnyEditor;
import edu.kit.iti.algover.gui.EditorFooterPanel;
import edu.kit.iti.algover.gui.EditorPanel;
import edu.kit.iti.algover.gui.GUICenter;
import edu.kit.iti.algover.gui.components.EditorTabbedPane;

import javax.swing.event.CaretEvent;
import javax.swing.event.CaretListener;

/**
 * Created by sarah on 9/27/16.
 */
public class FooterCaretListener implements CaretListener {
    GUICenter center;
    EditorFooterPanel footer;
    EditorPanel edPanel;
    EditorTabbedPane tabbedPane;
    DafnyEditor currentTextArea;


    public FooterCaretListener(GUICenter center){
        this.center = center;

    }

    @Override
    public void caretUpdate(CaretEvent e) {
        this.edPanel = center.getMainwindow().getEditorPanel();
        this.footer = this.edPanel.getFooter();
        this.tabbedPane = this.edPanel.getTabbedPane();
        this.currentTextArea = tabbedPane.getFocusTab();
        if(this.currentTextArea != null){
            int i = this.currentTextArea.getCaretLineNumber() + 1;
            String line = Integer.toString(i);
            System.out.println(i);
            footer.setRightLabelTest("line "+line);
        }



    }


}
