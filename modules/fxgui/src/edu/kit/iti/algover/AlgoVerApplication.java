package edu.kit.iti.algover;

import javafx.application.Application;
import javafx.scene.Scene;
import javafx.scene.control.TextField;
import javafx.stage.Stage;

/**
 * Created by Philipp on 15.06.2017.
 */
public class AlgoVerApplication extends Application {

  @Override
  public void start(Stage primaryStage) throws Exception {
    primaryStage.setScene(new Scene(new TextField("HI")));
    primaryStage.show();
  }
}
