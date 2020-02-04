package edu.kit.iti.algover.browser.entities;

import edu.kit.iti.algover.dafnystructures.DafnyDecl;

public class DafnyEntityGetterVisitor implements TreeTableEntityVisitor<DafnyDecl> {
    @Override
    public DafnyDecl visitMethod(MethodEntity entity) {
        return entity.getDafnyMethod();
    }

    @Override
    public DafnyDecl visitFile(FileEntity entity) {
        return entity.getDafnyFile();
    }

    @Override
    public DafnyDecl visitClass(ClassEntity entity) {
        return entity.getDafnyClass();
    }

    @Override
    public DafnyDecl visitPVC(PVCEntity entity) {
        return null;
    }

    @Override
    public DafnyDecl visitPVCGroup(PVCGroupEntity group) {
        return null;
    }

    @Override
    public DafnyDecl visitOther(OtherEntity entity) {
        return null;
    }

    @Override
    public DafnyDecl visitFunction(FunctionEntity functionEntity) {
        return functionEntity.getDafnyFunction();
    }
}
