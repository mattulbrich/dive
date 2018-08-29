/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 *
 */

package edu.kit.iti.algover.dafnystructures;

import edu.kit.iti.algover.parser.DafnyParser;
import edu.kit.iti.algover.parser.DafnyTree;
import edu.kit.iti.algover.term.FunctionSymbol;
import edu.kit.iti.algover.term.Sort;
import edu.kit.iti.algover.util.TreeUtil;

import java.util.List;

/**
 * A function symbol which captures a function defined in Dafny.
 *
 * The only real difference to a usual {@link FunctionSymbol} is that this class
 * contains a reference to a {@link DafnyFunction}.
 *
 * The name and types are computed from the DafnyFunction.
 *
 * If the function is toplevel (not in a class), then the logical name is
 * {@code $$name}. If it is defined in a class C, the name is {@code C$$name}.
 *
 * @author mulbrich
 */
public class DafnyFunctionSymbol extends FunctionSymbol {

    private DafnyFunction origin;

    public DafnyFunctionSymbol(DafnyFunction origin) {
        super(computeName(origin),
                TreeUtil.toSort(origin.getReturnType()),
                computeArgs(origin));
        this.origin = origin;
    }

    private static String computeName(DafnyFunction f) {
        DafnyDecl parent = f.getParentDecl();
        StringBuilder sb = new StringBuilder();
        if (parent instanceof DafnyClass) {
            sb.append(parent.getName());
        }
        sb.append("$$").append(f.getName());
        return sb.toString();
    }

    private static Sort[] computeArgs(DafnyFunction f) {
        Sort[] args;
        List<DafnyTree> parameters = f.getParameters();
        DafnyDecl parent = f.getParentDecl();
        if (parent instanceof DafnyClass) {
            DafnyClass clss = (DafnyClass) parent;
            args = new Sort[parameters.size() + 2];
            args[0] = Sort.HEAP;
            args[1] = Sort.getClassSort(clss.getName());
            for (int i = 2; i < args.length; i++) {
                args[i] = TreeUtil.toSort(parameters.get(i - 2).
                        getFirstChildWithType(DafnyParser.TYPE).getChild(0));
            }
        } else {
            args = new Sort[parameters.size() + 1];
            args[0] = Sort.HEAP;
            for (int i = 1; i < args.length; i++) {
                args[i] = TreeUtil.toSort(parameters.get(i-1).
                        getFirstChildWithType(DafnyParser.TYPE).getChild(0));
            }
        }
        return args;
    }

    public DafnyFunction getOrigin() {
        return origin;
    }
}
