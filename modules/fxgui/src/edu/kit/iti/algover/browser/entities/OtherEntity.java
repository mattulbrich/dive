package edu.kit.iti.algover.browser.entities;

import java.util.List;

/**
 * Created by philipp on 12.07.17.
 */
public class OtherEntity extends TreeTableEntity {

    public OtherEntity(String text, List<TreeTableEntity> children) {
        super(text, null, children);
    }

    @Override
    public <T> T accept(TreeTableEntityVisitor<T> visitor) {
        return visitor.visitOther(this);
    }
}
