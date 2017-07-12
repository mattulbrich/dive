package edu.kit.iti.algover.browser.entities;

import edu.kit.iti.algover.dafnystructures.DafnyFile;
import edu.kit.iti.algover.proof.PVC;

/**
 * Created by philipp on 12.07.17.
 */
public class PVCEntity extends TreeTableEntity {

    private final PVC pvc;

    public PVCEntity(PVC pvc, DafnyFile location) {
        super(pvc.getName(), location);
        this.pvc = pvc;
    }

    @Override
    public <T> T accept(TreeTableEntityVisitor<T> visitor) {
        return visitor.visitPVC(this);
    }

    public PVC getPVC() {
        return pvc;
    }

}
