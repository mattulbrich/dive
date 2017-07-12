package edu.kit.iti.algover.browser.entities;

import edu.kit.iti.algover.dafnystructures.DafnyFile;
import edu.kit.iti.algover.proof.PVCGroup;

/**
 * Created by philipp on 12.07.17.
 */
public class PVCGroupEntity extends TreeTableEntity {

    private final PVCGroup group;

    public PVCGroupEntity(PVCGroup group, DafnyFile location) {
        super("proof verification condition group", location);
        this.group = group;
    }

    @Override
    public <T> T accept(TreeTableEntityVisitor<T> visitor) {
        return visitor.visitPVCGroup(this);
    }

    public PVCGroup getGroup() {
        return group;
    }

}
