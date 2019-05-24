package edu.kit.iti.algover.util;

import javafx.scene.control.Alert;
import javafx.scene.control.Label;
import javafx.scene.control.TextArea;
import javafx.scene.layout.VBox;

import java.io.PrintWriter;
import java.io.StringWriter;

public class ExceptionDialog extends Alert {

    private Throwable exception;

    private VBox content;

    public ExceptionDialog(Throwable e) {
        super(AlertType.ERROR);
        this.exception = e;
        this.setHeaderText("An error occured: "+ e.getMessage());

        content = new VBox();

        TextArea area = new TextArea();
        area.setEditable(false);
        StringWriter sw = new StringWriter();
        PrintWriter pw = new PrintWriter(sw);

        e.printStackTrace(pw);
        String s = pw.toString();
        area.setText(s);

        content.getChildren().addAll(new Label("Stacktrace"), area);
        this.getDialogPane().setContent(content);

    }



    public Throwable getException() {
        return exception;
    }

    public void setException(Throwable e){
        this.exception = e;
    }
}
