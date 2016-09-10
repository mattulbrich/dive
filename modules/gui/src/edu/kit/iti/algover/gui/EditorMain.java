package edu.kit.iti.algover.gui;

import java.io.File;
import java.io.IOException;

/**
 * EditorMain constructs an object of EditorWindow.
 * EditorWindow contains a menu bar, a toolbar and a panel for a text area.
 *
 * Created by sony on 06.09.2016.
 */

public class EditorMain {

    static  String filename = "D"+ File.separator+"...";

    public static void main ( String[] args ) throws IOException
    {
        File f = new File(filename);

        MenuBar menuBar = new MenuBar();
        ToolBar toolbar = new ToolBar();
        EditorPanel panel = new EditorPanel();

        EditorWindow window1 = new EditorWindow( menuBar, toolbar, panel );
        window1.setSize( 700, 500 );
        window1.setVisible( true );
    }
}
