/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.project;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import edu.kit.iti.algover.dafnystructures.DafnyClass;
import edu.kit.iti.algover.dafnystructures.DafnyField;
import edu.kit.iti.algover.dafnystructures.DafnyFunction;
import edu.kit.iti.algover.dafnystructures.DafnyMethod;
import edu.kit.iti.algover.parser.DafnyTree;
import edu.kit.iti.algover.term.FunctionSymbol;
import edu.kit.iti.algover.term.Sort;
import edu.kit.iti.algover.util.TreeUtil;

// REVIEW: Document!

public class DeclarationSymbolCollector {

    private final List<FunctionSymbol> collected = new ArrayList<>();

    public static Collection<FunctionSymbol> collect(Project project) {
        DeclarationSymbolCollector dsc = new DeclarationSymbolCollector();
        dsc.collectProject(project);
        return dsc.collected;
    }

    private void collectProject(Project project) {
        for (DafnyClass clss : project.getClasses()) {
            collectClass(clss);
        }
        for (DafnyMethod m : project.getMethods()) {
            collectMethod(null, m);
        }
        for (DafnyFunction f : project.getFunctions()) {
            collectFunction(null, f);
        }
    }

    private void collectClass(DafnyClass clss) {

        for (DafnyField field : clss.getFields()) {
            Sort result = TreeUtil.toSort(field.getType());
            Sort container = new Sort(clss.getName());
            Sort sort = new Sort("field", container, result);
            String name = clss.getName() + "$" + field.getName();
            collected.add(new FunctionSymbol(name, sort));
        }

        for (DafnyMethod m : clss.getMethods()) {
            collectMethod(clss, m);
        }
        for (DafnyFunction f : clss.getFunctions()) {
            collectFunction(clss, f);
        }
    }

    private void collectFunction(DafnyClass clss, DafnyFunction f) {
        Sort result = TreeUtil.toSort(f.getReturnType());
        Sort[] args;
        List<DafnyTree> parameters = f.getParameters();
        String name;
        if(clss == null) {
            name = "$$" + f.getName();
            args = new Sort[parameters.size() + 1];
            args[0] = Sort.HEAP;
            for (int i = 1; i < args.length; i++) {
                args[i] = TreeUtil.toSort(parameters.get(i-1).getChild(1));
            }
        } else {
            name = clss.getName() + "$$" + f.getName();
            args = new Sort[parameters.size() + 2];
            args[0] = Sort.HEAP;
            args[1] = new Sort(clss.getName());
            for (int i = 2; i < args.length; i++) {
                args[i] = TreeUtil.toSort(parameters.get(i-2).getChild(1));
            }
        }

        collected.add(new FunctionSymbol(name, result, args));
    }

    private void collectMethod(DafnyClass clss, DafnyMethod m) {
        // currently methods cannot appear as logic symbols
    }

}
