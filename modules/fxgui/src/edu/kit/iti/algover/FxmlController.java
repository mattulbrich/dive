package edu.kit.iti.algover;

import javafx.fxml.FXMLLoader;
import javafx.scene.Parent;

import java.io.IOException;

public abstract class FxmlController {

    protected final Parent view;

    public FxmlController(String viewFxml) {
        long before = System.currentTimeMillis();

        FXMLLoader loader = new FXMLLoader(getClass().getResource(viewFxml));
        loader.setController(this);
        try {
            loader.load();
        } catch (IOException e) {
            e.printStackTrace();
        }
        this.view = loader.getRoot();

        System.out.println("Load time of " + viewFxml + ": " + (System.currentTimeMillis() - before) + "ms.");
    }

    public Parent getView() {
        return view;
    }
}
