package edu.kit.iti.algover.browser.entities;

/**
 * Created by philipp on 12.07.17.
 */
public class OtherEntity extends TreeTableEntity {

    public OtherEntity(String text) {
        super(text, null);
    }

    @Override
    public <T> T accept(TreeTableEntityVisitor<T> visitor) {
        return visitor.visitOther(this);
    }
}
