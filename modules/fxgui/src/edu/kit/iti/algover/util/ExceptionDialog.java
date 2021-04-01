package edu.kit.iti.algover.util;

import javafx.application.Platform;
import javafx.scene.control.Alert;
import javafx.scene.control.Label;
import javafx.scene.control.TextArea;
import javafx.scene.layout.BorderPane;
import javafx.scene.layout.VBox;

import java.io.PrintWriter;
import java.io.StringWriter;

// TODO PLEASE document such classes, PLEASE.
public class ExceptionDialog extends Alert {

    private Throwable exception;

    private BorderPane content;

    public ExceptionDialog(Throwable e) {
        super(AlertType.ERROR);
        this.exception = e;
        this.setHeaderText("An error occured: "+ e.getMessage());

        content = new BorderPane();

        TextArea area = new TextArea();
        StringWriter sw = new StringWriter();
        PrintWriter pw = new PrintWriter(sw);
        
        e.printStackTrace(pw);
        String s = sw.toString();
        // System.out.println("s = " + s);
        area.setText(s);
        area.setEditable(false);

        content.setCenter(area);

        this.getDialogPane().setContent(content);
        this.setResizable(true);
        this.onShownProperty().addListener(eObservable -> {
            Platform.runLater(() -> this.setResizable(false));
        });

    }



    public Throwable getException() {
        return exception;
    }

    public void setException(Throwable e){
        this.exception = e;
    }
}
