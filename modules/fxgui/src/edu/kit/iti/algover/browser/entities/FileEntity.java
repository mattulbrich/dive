/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.browser.entities;

import edu.kit.iti.algover.dafnystructures.DafnyFile;

import java.util.List;

/**
 * Created by philipp on 12.07.17.
 */
public class FileEntity extends TreeTableEntity {

    public FileEntity(DafnyFile file, List<TreeTableEntity> children) {
        super(file.getFilename(), file, children);
    }

    @Override
    public <T> T accept(TreeTableEntityVisitor<T> visitor) {
        return visitor.visitFile(this);
    }

    public DafnyFile getDafnyFile() {
        return getLocation();
    }

}
