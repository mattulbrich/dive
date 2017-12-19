package edu.kit.iti.algover.browser;

import edu.kit.iti.algover.browser.entities.*;
import javafx.scene.Node;
import javafx.scene.control.Label;
import javafx.scene.paint.Color;

/**
 * Created by philipp on 12.07.17.
 */
public class TreeTableEntityNameRenderer implements TreeTableEntityVisitor<Node> {

    public static final TreeTableEntityNameRenderer INSTANCE = new TreeTableEntityNameRenderer();

    @Override
    public Node visitMethod(MethodEntity entity) {
        return blueLabel("method");
    }

    @Override
    public Node visitFile(FileEntity entity) {
        return null;
    }

    @Override
    public Node visitClass(ClassEntity entity) {
        return blueLabel("class");
    }

    @Override
    public Node visitPVC(PVCEntity entity) {
        return null; //return GlyphsDude.createIcon(FontAwesomeIcon.CIRCLE_ALT);
    }

    @Override
    public Node visitPVCGroup(PVCGroupEntity group) {
        return null; //return GlyphsDude.createIcon(FontAwesomeIcon.CIRCLE_ALT);
    }

    @Override
    public Node visitOther(OtherEntity entity) {
        return null;
    }

    private Node blueLabel(String text) {
        Label label = new Label(text);
        label.setTextFill(Color.BLUE);
        return label;
    }
}
