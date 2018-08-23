package edu.kit.iti.algover.util;


import javafx.application.Platform;
import javafx.event.ActionEvent;
import javafx.scene.control.Button;
import javafx.scene.control.Dialog;
import javafx.scene.control.Label;
import javafx.scene.control.ProgressBar;
import javafx.scene.layout.VBox;
import javafx.stage.Window;

/**
 * Created by jklamroth on 8/21/18.
 */
public class ProgressBarDialog extends Dialog {
    ProgressBar pb;
    VBox vBox;
    String endMessage;
    int maxSteps;
    int currentProgress = 0;

    public ProgressBarDialog(String title, String message, String endMessage) {
        super();
        this.setTitle(title);
        this.endMessage = endMessage;

        Window window = this.getDialogPane().getScene().getWindow();
        window.setOnCloseRequest(event -> {
            window.hide();
        });

        vBox = new VBox(10.0);
        Label l = new Label(message);
        pb = new ProgressBar();

        vBox.getChildren().addAll(l, pb);
        this.getDialogPane().setContent(vBox);
    }

    public void setMaxSteps(int maxSteps) {
        this.maxSteps = maxSteps;
    }

    public void nextProgressStep() {
        currentProgress++;
        updateProgress((double)currentProgress / (double) maxSteps);
    }

    public void setCurrentProgress(int i) {
        currentProgress = i;
        updateProgress((double)currentProgress / (double) maxSteps);
    }

    public void updateProgress(double p) {
        if(p < 0.0 || p > 1.0) {
            throw new IllegalArgumentException("Progress must be between 0.0 and 1.0");
        }
        Platform.runLater(() -> {
            pb.setProgress(p);
        });

        System.out.println(p);

        if(p == 1.0) {
            Window window = this.getDialogPane().getScene().getWindow();
            vBox.getChildren().add(new Label(endMessage));
            Button button = new Button("Ok");
            button.setOnAction(event -> {
                window.hide();
            });
            vBox.getChildren().add(button);
            getDialogPane().requestLayout();
        }
    }
}
