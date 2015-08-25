package edu.kit.iti.algover.ui.gui;

import edu.kit.iti.algover.ui.controller.ProgrammeViewController;
import edu.kit.iti.algover.ui.util.ConfirmBox;
import javafx.scene.control.Menu;
import javafx.scene.control.MenuBar;
import javafx.scene.control.MenuItem;
import javafx.stage.Stage;

/**
 * Created by sarah on 8/25/15.
 */
public class TopMenu extends MenuBar {


//    MenuBar topMenu;

    //different Menus
    Menu fileMenu;
    Menu optionsMenu;
    Menu aboutMenu;
    Menu menuView;

    MenuItem loadFile;
    MenuItem quit;
    MenuItem pView;
    MenuItem seqView;
    MenuItem scriptView;
    Stage primaryStage;

    public TopMenu(Stage primaryStage){
        super();
        this.primaryStage = primaryStage;
        fileMenu = new Menu("File");
        loadFile = new MenuItem("Load file...");
        quit = new MenuItem("Quit");

        fileMenu.getItems().addAll(loadFile, quit);

        optionsMenu = new Menu("Options");
        aboutMenu = new Menu("About");


        menuView  = new Menu("View");

        pView  = new MenuItem("Open Src View");
        seqView  = new MenuItem("Open Sequent View");
        scriptView  = new MenuItem("Open Proofscript View");
        menuView.getItems().addAll(pView, seqView, scriptView);
        this.getMenus().addAll(fileMenu, optionsMenu, menuView, aboutMenu);
        addActions();
    }

    public MenuBar getTopMenu(){
        return this;
    }
    private void addActions(){
        pView.setOnAction(e ->{
            ProgrammeViewController pviewC = new ProgrammeViewController();
            try {
                pviewC.start(primaryStage);
            } catch (Exception e1) {
                e1.printStackTrace();
            }
        });
        quit.setOnAction(e->{
            Boolean answer = ConfirmBox.display("Closing", "Are you sure you want to close the application?");
                if(answer){
                    primaryStage.close();

                }

        });
        //loadFile.setOnAction( e -> );

    }
}
