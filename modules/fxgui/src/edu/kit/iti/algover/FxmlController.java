/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
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
            System.err.println("Could not load .fxml, maybe the filename was incorrect / the file was not configured to be a resource.");
            e.printStackTrace();
        }
        this.view = loader.getRoot();

        System.out.println("Load time of " + viewFxml + ": " + (System.currentTimeMillis() - before) + "ms.");
    }

    public Parent getView() {
        return view;
    }
}
