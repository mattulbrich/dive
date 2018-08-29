package edu.kit.iti.algover.util;


import javafx.application.Platform;
import javafx.event.ActionEvent;
import javafx.geometry.Pos;
import javafx.scene.control.Button;
import javafx.scene.control.Dialog;
import javafx.scene.control.Label;
import javafx.scene.control.ProgressBar;
import javafx.scene.layout.HBox;
import javafx.scene.layout.VBox;
import javafx.stage.Window;

/**
 * Created by jklamroth on 8/21/18.
 */
public class ProgressBarDialog extends Dialog {
    ProgressBar pb;
    VBox vBox;
    String endMessage;
    Label endMessageLabel;
    Button okButton;
    int maxSteps;
    int currentProgress = 0;
    int failedSteps = 0;

    public ProgressBarDialog(String title, String message) {
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

        endMessageLabel = new Label(maxSteps - failedSteps + " goals were closed \n" + failedSteps + " still remain open");
        vBox.getChildren().add(endMessageLabel);
        okButton = new Button("Ok");
        okButton.setOnAction(event -> {
            window.hide();
        });
        endMessageLabel.setVisible(false);
        okButton.setVisible(false);
        HBox hb = new HBox();
        hb.setAlignment(Pos.BASELINE_CENTER);
        hb.getChildren().add(okButton);
        vBox.getChildren().add(hb);

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

        if(p == 1.0) {
            Platform.runLater(() -> {
                endMessageLabel.setText(maxSteps - failedSteps + " goals were closed \n" + failedSteps + " still remain open");
                endMessageLabel.setVisible(true);
                okButton.setVisible(true);
            });

        }
    }

    public void incFailed() {
        failedSteps++;
    }
}
