package edu.kit.iti.algover.browser;

import de.jensd.fx.glyphs.GlyphsDude;
import de.jensd.fx.glyphs.fontawesome.FontAwesomeIcon;
import edu.kit.iti.algover.browser.entities.*;
import javafx.scene.Node;
import javafx.scene.control.Label;
import javafx.scene.control.Tooltip;
import javafx.scene.paint.Color;
import javafx.scene.text.Text;

public class TreeTableEntityStatusRenderer implements TreeTableEntityVisitor<Node> {

    public static final TreeTableEntityStatusRenderer INSTANCE = new TreeTableEntityStatusRenderer();

    private TreeTableEntityStatusRenderer() {
    }

    private Node groupingEntity(TreeTableEntity entity) {
        Label label = new Label(entity.getProvenChildren() + "/" + entity.getNumberChildren());
        if (entity.getProvenChildren() >= entity.getNumberChildren()) {
            Text icon = GlyphsDude.createIcon(FontAwesomeIcon.CHECK);
            icon.setFill(Color.LIMEGREEN);
            label.setGraphic(icon);
            label.setTooltip(new Tooltip("All PVCs proven"));
        } else {
            label.setTooltip(new Tooltip(
                    entity.getProvenChildren()
                            + " from " + entity.getNumberChildren()
                            + " PVCs proven"));
        }
        return label;
    }

    @Override
    public Node visitPVC(PVCEntity entity) {
        Label label = new Label();
        Text icon = GlyphsDude.createIcon(entity.getProofStatus().getIcon());
        icon.setFill(entity.getProofStatus().getFill());
        label.setTooltip(new Tooltip(entity.getProofStatus().getTooltip()));
        label.setGraphic(icon);
        return label;
    }

    @Override
    public Node visitMethod(MethodEntity entity) {
        return groupingEntity(entity);
    }

    @Override
    public Node visitFile(FileEntity entity) {
        return groupingEntity(entity);
    }

    @Override
    public Node visitClass(ClassEntity entity) {
        return groupingEntity(entity);
    }

    @Override
    public Node visitPVCGroup(PVCGroupEntity group) {
        return groupingEntity(group);
    }

    @Override
    public Node visitOther(OtherEntity entity) {
        return groupingEntity(entity);
    }
}
