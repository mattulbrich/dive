package edu.kit.iti.algover.browser;

import edu.kit.iti.algover.browser.entities.*;
import javafx.scene.Node;
import javafx.scene.control.Label;
import javafx.scene.paint.Color;

/**
 * Created by philipp on 12.07.17.
 */
public class TreeTableEntityRenderer implements TreeTableEntityVisitor<Node> {

    public static final TreeTableEntityRenderer INSTANCE = new TreeTableEntityRenderer();

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
        return new Label("•"); // TODO: this can be just a _little_ more beautiful
    }

    @Override
    public Node visitPVCGroup(PVCGroupEntity group) {
        return new Label("•"); // TODO: here as well (see ^)
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
