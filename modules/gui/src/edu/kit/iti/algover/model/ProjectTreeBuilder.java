package edu.kit.iti.algover.model;

import edu.kit.iti.algover.dafnystructures.DafnyClass;
import edu.kit.iti.algover.dafnystructures.DafnyField;
import edu.kit.iti.algover.dafnystructures.DafnyFunction;
import edu.kit.iti.algover.dafnystructures.DafnyMethod;
import edu.kit.iti.algover.project.Project;

import java.util.LinkedList;
import java.util.List;

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
        List<DafnyMethod> methods = p.getMethods();
        List<DafnyFunction> functions = p.getFunctions();
        List<DafnyClass> classes = p.getClasses();


        LinkedList<ProjectTree> children = new LinkedList<>();

        ProjectTree projectTree = new ProjectTree("Project");
        projectTree.setParent(null);

        if(methods.size() > 0) {

            ProjectTree methodTree = new ProjectTree("Methods");
            methodTree.setParent(projectTree);

            List<ProjectTree> methodLeaves = new LinkedList<>();
            for (DafnyMethod m : methods) {
                methodLeaves.add(new MethodLeaf(m, methodTree));
            }
            methodTree.setChildren(methodLeaves);
            children.add(methodTree);

        }

        if(classes.size() > 0) {
            ProjectTree classTree = new ProjectTree("Classes");
            classTree.setParent(projectTree);
            LinkedList<ProjectTree> classTrees = new LinkedList<>();
            for (DafnyClass dClass : classes) {
                classTrees.add(createClassSubTree(dClass, classTree));
            }
            classTree.setChildren(classTrees);
            children.add(classTree);
        }

        if(functions.size() > 0) {

            ProjectTree functionTree = new ProjectTree("Functions");
            functionTree.setParent(projectTree);
            List<ProjectTree> functionLeaves = new LinkedList<>();
            for (DafnyFunction f : functions) {
                functionLeaves.add(new FunctionLeaf(f, functionTree));
            }
            functionTree.setChildren(functionLeaves);
            children.add(functionTree);
        }

        projectTree.setChildren(children);
        return projectTree;
    }

    private ProjectTree createClassSubTree(DafnyClass dClass, ProjectTree parentTree){

        ProjectTree classTree = new ProjectTree("Class: "+dClass.getName());
        classTree.setParent(parentTree);

        LinkedList<ProjectTree> children = new LinkedList<>();

        List<DafnyFunction> functions = dClass.getFunctions();
        List<DafnyMethod> methods = dClass.getMethods();
        List<DafnyField> fields = dClass.getFields();


        if (methods.size() > 0) {

            //methods
            ProjectTree methodTree = new ProjectTree("Methods");
            methodTree.setParent(classTree);
            List<ProjectTree> methodLeaves = new LinkedList<>();
            for (DafnyMethod m : methods) {
                methodLeaves.add(new MethodLeaf(m, methodTree));
            }
            methodTree.setChildren(methodLeaves);
            children.add(methodTree);
        }
        if (fields.size() > 0) {

            //fields
            ProjectTree fieldTree = new ProjectTree("Fields");
            fieldTree.setParent(classTree);
            List<ProjectTree> fieldLeaves = new LinkedList<>();
            for (DafnyField f : fields) {
                fieldLeaves.add(new FieldLeaf(f, fieldTree));
            }
            fieldTree.setChildren(fieldLeaves);
            children.add(fieldTree);
        }

        if (functions.size() > 0) {

            //functions
            ProjectTree functionTree = new ProjectTree("Functions");
            functionTree.setParent(classTree);
            List<ProjectTree> functionLeaves = new LinkedList<>();
            for (DafnyFunction f : functions) {
                functionLeaves.add(new FunctionLeaf(f, functionTree));
            }
            functionTree.setChildren(functionLeaves);
            children.add(functionTree);
        }
        classTree.setChildren(children);
        return classTree;
    }
}
