package edu.kit.iti.algover;


import com.google.common.base.Charsets;
import com.google.common.io.CharStreams;
import javafx.application.Platform;
import javafx.scene.control.Alert;
import javafx.scene.web.WebEngine;
import javafx.scene.web.WebView;

import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;

public class AboutWindow extends Alert {


    public AboutWindow() throws IOException {
        super(AlertType.INFORMATION);
        this.setHeaderText("About");
        WebView webView = new WebView();
        InputStream resourceAsStream = getClass().getResourceAsStream("About.html");
        String text = CharStreams.toString(new InputStreamReader(resourceAsStream, Charsets.UTF_8));

        WebEngine engine = webView.getEngine();
        engine.setUserStyleSheetLocation(getClass().getResource("webView.css").toString());
        engine.loadContent(text);

        //workaround for KDE systems and GTK based Desktops
        this.setResizable(true);
        this.onShownProperty().addListener(e -> {
            Platform.runLater(() -> this.setResizable(false));
        });

        this.getDialogPane().setContent(webView);
    }
}
