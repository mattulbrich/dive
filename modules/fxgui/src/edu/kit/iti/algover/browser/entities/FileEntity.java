package edu.kit.iti.algover.browser.entities;

import edu.kit.iti.algover.dafnystructures.DafnyFile;

/**
 * Created by philipp on 12.07.17.
 */
public class FileEntity extends TreeTableEntity {

    public FileEntity(DafnyFile file) {
        super(file.getFilename(), file);
    }

    @Override
    public <T> T accept(TreeTableEntityVisitor<T> visitor) {
        return visitor.visitFile(this);
    }

    public DafnyFile getDafnyFile() {
        return getLocation();
    }

}
