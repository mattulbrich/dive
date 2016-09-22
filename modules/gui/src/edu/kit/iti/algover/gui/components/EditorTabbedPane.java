package edu.kit.iti.algover.gui.components;

import edu.kit.iti.algover.gui.DafnyEditor;
import edu.kit.iti.algover.gui.GUICenter;
import org.fife.ui.rtextarea.RTextScrollPane;

import javax.swing.*;
import java.io.File;

/**
 * TabbedPane for Editor with handy methods
 * Created by sarah on 9/22/16.
 */
public class EditorTabbedPane extends JTabbedPane {
    GUICenter center;
    public EditorTabbedPane(GUICenter center){
        super();
        this.center = center;
    }

    /**
     * Searches whether tab with filename exists
     * @param name of file
     * @return index, -1 if it doesn't exist
     */
    public int tabWithNameExists(String name){
            int tabIndex = -1;
            for (int i = 0; i < this.getTabCount(); i++) {
                String tabName = this.getTitleAt(i);
                if (tabName != null && tabName.equals(name)) {
                    tabIndex = i;
               }
             }
        return tabIndex;
    }

    /**
     * Set the tab woth loaded file into focus if it exists create new one if it doesn't exist
     * @param loadedFile
     */
    public void setTabInFocus(File loadedFile){
        int tabCount = this.getTabCount();
        int tabIndex = tabWithNameExists(loadedFile.getName());
       if( tabIndex > -1){
            this.setSelectedIndex(tabIndex);
       }else{
         //create new tab
        try {
            DafnyEditor textarea = new DafnyEditor(loadedFile, center);
            textarea.setSrcText(loadedFile);
            EditorScrollPane sp = new EditorScrollPane(textarea);
            sp.setName(loadedFile.getName());

            this.addTab(loadedFile.getName(), sp);
            this.setSelectedIndex(tabCount);
        } catch (Exception e) {
            JOptionPane.showMessageDialog(center.getMainwindow(),
                    "Unable to load file " + center.getLoadedDafnySrc(),
                    "Source File Loading",
                    JOptionPane.ERROR_MESSAGE);

        }

        }

    }

    public EditorScrollPane getTabWithName(String filename){
            for (int i = 0; i < this.getTabCount(); i++) {
                String tabName = this.getTitleAt(i);
                if (tabName != null && tabName.equals(filename)) {
                    return (EditorScrollPane) this.getComponentAt(i);
               }
             }
        return null;
    }
}


