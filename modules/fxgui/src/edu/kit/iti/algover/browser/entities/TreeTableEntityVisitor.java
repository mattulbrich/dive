package edu.kit.iti.algover.browser.entities;

import edu.kit.iti.algover.proof.PVCGroup;

/**
 * Created by philipp on 12.07.17.
 */
public interface TreeTableEntityVisitor<T> {

    T visitMethod(MethodEntity entity);
    T visitFile(FileEntity entity);
    T visitClass(ClassEntity entity);
    T visitPVC(PVCEntity entity);
    T visitPVCGroup(PVCGroupEntity group);
    T visitOther(OtherEntity entity);
}
