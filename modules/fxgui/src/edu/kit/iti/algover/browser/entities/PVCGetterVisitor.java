package edu.kit.iti.algover.browser.entities;

import edu.kit.iti.algover.browser.entities.*;
import edu.kit.iti.algover.proof.PVC;

/**
 * Created by philipp on 12.07.17.
 */
public class PVCGetterVisitor implements TreeTableEntityVisitor<PVC> {
    @Override
    public PVC visitMethod(MethodEntity entity) {
        return null;
    }

    @Override
    public PVC visitFile(FileEntity entity) {
        return null;
    }

    @Override
    public PVC visitClass(ClassEntity entity) {
        return null;
    }

    @Override
    public PVC visitPVC(PVCEntity entity) {
        return entity.getPVC();
    }

    @Override
    public PVC visitPVCGroup(PVCGroupEntity group) {
        return null;
    }

    @Override
    public PVC visitOther(OtherEntity entity) {
        return null;
    }
}
