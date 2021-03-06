/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.util;

import javafx.geometry.Bounds;
import javafx.scene.Group;
import javafx.scene.Scene;
import javafx.scene.text.Text;

import java.util.List;

/**
 * Created by Philipp on 24.07.2017.
 */
public class TextUtil {

    public static Bounds computeTextBounds(String text, List<String> styleClasses, List<String> stylesheets) {
        return computeTextBounds(text, styleClasses, stylesheets, 0);
    }

    public static Bounds computeTextBounds(String text, List<String> styleClasses, List<String> stylesheets, int fontsize) {


        final Text textNode = new Text(text);
        textNode.getStyleClass().setAll(styleClasses);
        new Scene(new Group(textNode)).getStylesheets().setAll(stylesheets);
        if (fontsize > 0) {
            textNode.setStyle("-fx-font-size:"+fontsize+"pt;");
        }
        textNode.applyCss();
        return textNode.getLayoutBounds();
    }
}
