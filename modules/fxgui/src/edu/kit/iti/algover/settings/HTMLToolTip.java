package edu.kit.iti.algover.settings;

import javafx.scene.control.ContentDisplay;
import javafx.scene.control.Tooltip;
import javafx.scene.web.WebEngine;
import javafx.scene.web.WebView;

/**
 * Class to create a Tooltip containing HTML content
 * @author S.Grebing
 */
public class HTMLToolTip extends Tooltip {

    WebView contentView = new WebView();

    WebEngine contentEngine;

    public HTMLToolTip(String htmlContent){
        contentEngine = contentView.getEngine();
        contentEngine.loadContent(htmlContent);
        this.setContentDisplay(ContentDisplay.GRAPHIC_ONLY);
        this.setGraphic(contentView);
    }

}
