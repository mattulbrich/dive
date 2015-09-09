package edu.kit.iti.algover.ui.controller;

import edu.kit.iti.algover.Main;
import edu.kit.iti.algover.ui.Model.ProblemLoader;
import javafx.event.ActionEvent;
import javafx.event.EventHandler;
import javafx.fxml.FXML;
import javafx.fxml.FXMLLoader;
import javafx.scene.Group;
import javafx.scene.Node;
import javafx.scene.Parent;
import javafx.scene.Scene;
import javafx.scene.control.*;
import javafx.scene.text.Text;
import javafx.stage.FileChooser;
import javafx.stage.Modality;
import javafx.stage.Stage;
import javafx.stage.StageStyle;


import java.awt.peer.SystemTrayPeer;
import java.io.*;

/**
 * Created by sarah on 8/12/15.
 */
public class AlgoVerifGuiController {

    //protected Parent root;

    @FXML
    private TextArea srcPane;
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
        ProblemLoader.readFile(file);
        String text= "";
        String textline="";
        int line= 1;
        BufferedReader br = readFile(file);

        if(br != null) {

            while (textline != null) {
                try {
                    textline=  br.readLine();
                    text += line + ": " + textline + "\n";
                    line++;
                } catch (IOException e) {
                    e.printStackTrace();
                }

            }
            try {
                br.close();
            } catch (IOException e) {
                e.printStackTrace();
            }
            srcPane.setText(text);



        }else {
            srcPane.setText("File not read");
            // Main.readFile(file);
        }

    }
    @FXML
    private void handleListSelectAction(ActionEvent event){
        System.out.println("Select");
    }
    public void setStage(Stage stage){
        this.stage = stage;
    }
    public static BufferedReader readFile(File file) {
        try {
            BufferedReader br = new BufferedReader(new FileReader(file));
            return br;


        } catch (FileNotFoundException e) {
            System.out.println("Could not read file " + file.getAbsolutePath());
        } catch (Exception e) {
            System.out.println("Could not load problem");
        }return null;

    }
}
