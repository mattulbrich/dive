package edu.kit.iti.algover.browser;

import edu.kit.iti.algover.browser.entities.*;
import edu.kit.iti.algover.proof.PVC;

import java.util.ArrayList;
import java.util.List;

public class TreeTableEntityContextMenuStrategyHelper implements TreeTableEntityVisitor<List<String>> {
    @Override
    public List<String> visitMethod(MethodEntity entity) {
        return applyOnAllChildren(entity.getChildren());
    }

    @Override
    public List<String> visitFile(FileEntity entity) {
        //System.out.println("entity.getText() = " + entity.getText());
        return null;
    }

    @Override
    public List<String> visitClass(ClassEntity entity) {
        return applyOnAllChildren(entity.getChildren());
    }

    @Override
    public List<String> visitPVC(PVCEntity entity) {
        PVC pvc = entity.accept(new PVCGetterVisitor());
        ArrayList<String> strings = new ArrayList<String>();
        strings.add(pvc.getIdentifier());
        return strings;

    }

    @Override
    public List<String> visitPVCGroup(PVCGroupEntity group) {
        //System.out.println("entity.getText() = " + group.getText());

        return null;
    }

    @Override
    public List<String> visitOther(OtherEntity entity) {
        List<TreeTableEntity> children = entity.getChildren();
        return applyOnAllChildren(children);

    }

    private List<String> applyOnAllChildren(List<TreeTableEntity> children) {
        List<String> strings = new ArrayList<>();
        children.forEach(treeTableEntity -> {
            strings.addAll(treeTableEntity.accept(this));
        });
        return strings;
    }

    @Override
    public List<String> visitFunction(FunctionEntity functionEntity) {
        return applyOnAllChildren(functionEntity.getChildren());
    }
}
