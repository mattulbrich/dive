/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.browser.entities;

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

    T visitFunction(FunctionEntity functionEntity);
}
