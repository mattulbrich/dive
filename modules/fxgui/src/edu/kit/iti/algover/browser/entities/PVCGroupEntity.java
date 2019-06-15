/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.browser.entities;

import edu.kit.iti.algover.dafnystructures.DafnyFile;
import edu.kit.iti.algover.proof.PVCGroup;

import java.util.List;

/**
 * Created by philipp on 12.07.17.
 */
public class PVCGroupEntity extends TreeTableEntity {

    private final PVCGroup group;

    public PVCGroupEntity(PVCGroup group, DafnyFile location, List<TreeTableEntity> children) {
        super("proof verification condition group", location, children);
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
