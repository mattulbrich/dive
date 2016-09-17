package edu.kit.iti.algover.gui;

import java.awt.event.WindowEvent;
import java.awt.event.WindowListener;
import java.io.File;
import java.io.IOException;

/**
 * EditorMain constructs an object of EditorWindow.
 * EditorWindow contains a menu bar, a toolbar, a panel for the text area, and a footer.
 *
 * Created by sony on 06.09.2016.
 */

public class EditorMain {

    static  String filename = "D"+ File.separator+"...";

    public static void main ( String[] args ) throws IOException
    {
        //GUICenter center = new GUICenter(window1);
        File f = new File(filename);

        //MenuBar menuBar = new MenuBar();
        //ToolBar toolbar = new ToolBar();
        //EditorPanel panel = new EditorPanel();
        //FooterPanel footerPanel = new FooterPanel();

  //     EditorWindow window1 = new EditorWindow( menuBar, toolbar, panel, footerPanel );

    //    window1.setSize( 700, 500 );
     //   window1.setVisible( true );


    }
}
