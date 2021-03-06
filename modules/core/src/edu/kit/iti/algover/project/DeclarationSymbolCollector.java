/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.project;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import edu.kit.iti.algover.dafnystructures.DafnyClass;
import edu.kit.iti.algover.dafnystructures.DafnyField;
import edu.kit.iti.algover.dafnystructures.DafnyFunction;
import edu.kit.iti.algover.dafnystructures.DafnyFunctionSymbol;
import edu.kit.iti.algover.dafnystructures.DafnyMethod;
import edu.kit.iti.algover.parser.DafnyParser;
import edu.kit.iti.algover.parser.DafnyTree;
import edu.kit.iti.algover.term.FunctionSymbol;
import edu.kit.iti.algover.term.Sort;
import edu.kit.iti.algover.term.builder.TermBuilder;
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
            Sort container = Sort.getClassSort(clss.getName());
            Sort sort = Sort.get("field", container, result);
            String name = TermBuilder.fieldName(clss.getName(), field.getName());
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
        collected.add(new DafnyFunctionSymbol(f));
    }

    private void collectMethod(DafnyClass clss, DafnyMethod m) {
        // currently methods cannot appear as logic symbols
    }

}
