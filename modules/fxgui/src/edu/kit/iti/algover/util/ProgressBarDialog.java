package edu.kit.iti.algover.util;


import javafx.application.Platform;
import javafx.event.ActionEvent;
import javafx.geometry.Pos;
import javafx.scene.control.Button;
import javafx.scene.control.ButtonBar.ButtonData;
import javafx.scene.control.ButtonType;
import javafx.scene.control.Dialog;
import javafx.scene.control.Label;
import javafx.scene.control.ProgressBar;
import javafx.scene.layout.HBox;
import javafx.scene.layout.VBox;
import javafx.stage.Modality;
import javafx.stage.Window;
import org.reactfx.util.TriFunction;

import java.util.function.BiFunction;

/**
 * Created by jklamroth on 8/21/18.
 */
public class ProgressBarDialog extends Dialog<Void> {
    private final Label label;
    private final ProgressBar progressBar;
    private boolean aborted;
    private int maxSteps;
    private int currentProgress = 0;
    private int failedSteps = 0;

    private TriFunction<Integer, Integer, Integer, String> labelUpdaterFunction =
        (prog, fail, total)-> "Progress: " + prog + " of " + total +
                (fail > 0 ? " with " + fail + " failure(s)" : "");

    public ProgressBarDialog(String title, String message) {
        this.setTitle(title);
        this.setHeaderText(message);

        // Ugly. But what else?
        setResizable(true);
        setOnCloseRequest(ev -> ev.consume());
        getDialogPane().setPrefSize(480, 200);

        this.initModality(Modality.APPLICATION_MODAL);

        ButtonType abortButton = new ButtonType("Abort", ButtonData.OTHER);
        getDialogPane().getButtonTypes().addAll(abortButton);

        final Button button = (Button) getDialogPane().lookupButton(abortButton);
        button.addEventFilter(ActionEvent.ACTION, ev -> {
            aborted = true;
            ev.consume();
        });

        label = new Label(message);
        progressBar = new ProgressBar();
        progressBar.setPrefWidth(480);
        VBox vBox = new VBox(10.0, progressBar, label);
        vBox.fillWidthProperty().setValue(true);

        this.getDialogPane().setContent(vBox);
    }

    public void setMaxSteps(int maxSteps) {
        this.maxSteps = maxSteps;
    }

    public void setLabelUpdaterFunction(TriFunction<Integer, Integer, Integer, String> labelUpdaterFunction) {
        this.labelUpdaterFunction = labelUpdaterFunction;
    }

    public void setProgress(int progress) {
        this.currentProgress = progress;
        updateProgress();
    }

    public void incrementProgress() {
        incrementProgress(true);
    }

    public void incrementProgress(boolean success) {
        if(!success) {
            failedSteps ++;
        }
        setProgress(currentProgress + 1);
    }

    private void updateProgress() {
        double p = currentProgress / (double) maxSteps;
        String labelText = labelUpdaterFunction.apply(currentProgress, failedSteps, maxSteps);

        Platform.runLater(() -> {
            progressBar.setProgress(p);
            label.setText(labelText);
            if(p == 1.0) {
                getDialogPane().getButtonTypes().remove(0);
                getDialogPane().getButtonTypes().add(ButtonType.OK);
            }
        });

    }

    public boolean isAborted() {
        return aborted;
    }
}
