package edu.kit.iti.algover.ui;

import edu.kit.iti.algover.Main;
import javafx.event.ActionEvent;
import javafx.event.EventHandler;
import javafx.fxml.FXML;
import javafx.fxml.FXMLLoader;
import javafx.scene.Group;
import javafx.scene.Node;
import javafx.scene.Parent;
import javafx.scene.Scene;
import javafx.scene.control.Button;
import javafx.scene.control.Label;
import javafx.scene.control.Menu;
import javafx.scene.control.MenuItem;
import javafx.scene.text.Text;
import javafx.stage.FileChooser;
import javafx.stage.Modality;
import javafx.stage.Stage;
import javafx.stage.StageStyle;

import java.awt.peer.SystemTrayPeer;
import java.io.File;

/**
 * Created by sarah on 8/12/15.
 */
public class AlgoVerifGuiController {

    //protected Parent root;



    @FXML
    protected Menu fileMenu;
    @FXML
    protected MenuItem guitItem;
    @FXML
    protected MenuItem openItem;

    private Stage stage;

    @FXML
    private void handleQuitAction(ActionEvent event){
        System.out.println("Bye Bye");
        System.exit(0);
    }

    @FXML
    private void handleOpenAction(ActionEvent event){

        FileChooser fileChooser = new FileChooser();
       // FileChooser.ExtensionFilter extFilter = new FileChooser.ExtensionFilter("TXT files (*.txt)", "*.txt");
       // fileChooser.getExtensionFilters().add(extFilter);
        File file = fileChooser.showOpenDialog(stage);
        Main.readFile(file);

    }
    @FXML
    private void handleListSelectAction(ActionEvent event){
        System.out.println("Select");
    }
    public void setStage(Stage stage){
        this.stage = stage;
    }

}
