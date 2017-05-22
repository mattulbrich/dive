/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.model;

import java.io.File;
import java.util.Collection;
import java.util.LinkedList;
import java.util.List;

import edu.kit.iti.algover.dafnystructures.DafnyClass;
import edu.kit.iti.algover.dafnystructures.DafnyField;
import edu.kit.iti.algover.dafnystructures.DafnyFunction;
import edu.kit.iti.algover.dafnystructures.DafnyMethod;
import edu.kit.iti.algover.project.Project;

/**
 * Created by sarah on 9/15/16.
 */
public class ProjectTreeBuilder {

    public ProjectTreeBuilder(){


    }

    public ProjectTree buildProject(Project p){
        return createProjectTree(p);
    }

    private ProjectTree createProjectTree(Project p){
        Collection<DafnyMethod> methods = p.getMethods();
        Collection<DafnyFunction> functions = p.getFunctions();
        Collection<DafnyClass> classes = p.getClasses();


        LinkedList<ProjectTree> children = new LinkedList<>();

        ProjectTree projectTree = new ProjectTree("Project", p.getBaseDir());
        projectTree.setParent(null);

        if(methods.size() > 0) {

            ProjectTree methodTree = new ProjectTree("Methods", p.getBaseDir());
            methodTree.setParent(projectTree);

            List<ProjectTree> methodLeaves = new LinkedList<>();
            for (DafnyMethod m : methods) {
                methodLeaves.add(new MethodLeaf(m, methodTree, p));
            }
            methodTree.setChildren(methodLeaves);
            children.add(methodTree);

        }

        if(classes.size() > 0) {
            ProjectTree classTree = new ProjectTree("Classes", p.getBaseDir());
            classTree.setParent(projectTree);
            LinkedList<ProjectTree> classTrees = new LinkedList<>();
            for (DafnyClass dClass : classes) {
                classTrees.add(createClassSubTree(dClass, classTree, p));
            }
            classTree.setChildren(classTrees);
            children.add(classTree);
        }

        if(functions.size() > 0) {

            ProjectTree functionTree = new ProjectTree("Functions", p.getBaseDir());
            functionTree.setParent(projectTree);
            List<ProjectTree> functionLeaves = new LinkedList<>();
            for (DafnyFunction f : functions) {
                functionLeaves.add(new FunctionLeaf(f, functionTree, p));
            }
            functionTree.setChildren(functionLeaves);
            children.add(functionTree);
        }

        projectTree.setChildren(children);
        return projectTree;
    }

    private ProjectTree createClassSubTree(DafnyClass dClass, ProjectTree parentTree, Project p){

        File file = new File(dClass.getFilename());
        ProjectTree classTree = new ProjectTree(dClass.getName(), file);
        classTree.setParent(parentTree);

        LinkedList<ProjectTree> children = new LinkedList<>();

        Collection<DafnyFunction> functions = dClass.getFunctions();
        Collection<DafnyMethod> methods = dClass.getMethods();
        List<DafnyField> fields = (List<DafnyField>) dClass.getFields();


        if (methods.size() > 0) {

            //methods
            // TODO project directory is missing
            ProjectTree methodTree = new ProjectTree("Methods", file);
            methodTree.setParent(classTree);
            List<ProjectTree> methodLeaves = new LinkedList<>();
            for (DafnyMethod m : methods) {
                methodLeaves.add(new MethodLeaf(m, methodTree, p));
            }
            methodTree.setChildren(methodLeaves);
            children.add(methodTree);
        }
        if (fields.size() > 0) {

            //fields
            ProjectTree fieldTree = new ProjectTree("Fields", file);
            fieldTree.setParent(classTree);
            List<ProjectTree> fieldLeaves = new LinkedList<>();
            for (DafnyField f : fields) {
                fieldLeaves.add(new FieldLeaf(f, fieldTree, p));
            }
            fieldTree.setChildren(fieldLeaves);
            children.add(fieldTree);
        }

        if (functions.size() > 0) {

            //functions p.getScript().getAbsolutePath() before
            ProjectTree functionTree = new ProjectTree("Functions", file);
            functionTree.setParent(classTree);
            List<ProjectTree> functionLeaves = new LinkedList<>();
            for (DafnyFunction f : functions) {
                functionLeaves.add(new FunctionLeaf(f, functionTree, p));
            }
            functionTree.setChildren(functionLeaves);
            children.add(functionTree);
        }
        classTree.setChildren(children);
        return classTree;
    }
}
