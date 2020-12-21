/*
 * This file is part of DIVE.
 *
 * DIVE is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * DIVE is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public LicenS* along with DIVE.  If not, see <https://www.gnu.org/licenses/>.
 */

package edu.kit.iti.algover.rule.script;

import edu.kit.iti.algover.PropertyManager;
import javafx.scene.control.Button;
import javafx.scene.control.ButtonType;
import javafx.scene.control.Dialog;
import javafx.scene.layout.HBox;
import javafx.scene.layout.Priority;
import javafx.scene.layout.VBox;
import javafx.scene.web.WebEngine;
import javafx.scene.web.WebView;


public class BlocklyView extends VBox {
    private final WebView webView;
    private final WebEngine engine;


    private final ScriptViewListener listener;

    private final Button btRunScript;
    private final Button btInsertCases;


    public BlocklyView(ScriptViewListener listener) {
        this.listener = listener;

        webView = new WebView();
        engine = webView.getEngine();

        btRunScript = new Button("Replay");
        btInsertCases = new Button("Insert cases");

        engine.setJavaScriptEnabled(true);
        engine.setOnAlert(event -> showAlert(event.getData()));






        // TODO: remove, debugging only
        PropertyManager.getInstance().currentProofNodeSelector.addListener(
                (observable, oldValue, newValue) -> {
                    System.out.println("Selected PN= " + newValue);
                }
        );

        initView();
    }

    private void initView() {

        btInsertCases.setOnAction(event -> {
            listener.onInsertCases();
        });

        HBox.setHgrow(btRunScript, Priority.ALWAYS);
        HBox.setHgrow(btInsertCases, Priority.ALWAYS);
        btRunScript.setPrefWidth(500000);
        btInsertCases.setPrefWidth(500000);
        this.getChildren().setAll(new HBox(btRunScript, btInsertCases), this.webView);
    }






    private void showAlert(String message) {
        Dialog<Void> alert = new Dialog<>();
        alert.getDialogPane().setContentText(message);
        alert.getDialogPane().getButtonTypes().add(ButtonType.OK);
        alert.showAndWait();
    }

    public void update(String html) {
        engine.loadContent(html);
    }

    public WebEngine getEngine() {
        return engine;
    }
}
