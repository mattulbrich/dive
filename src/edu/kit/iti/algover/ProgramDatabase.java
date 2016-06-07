/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015 Karlsruhe Institute of Technology
 */

package edu.kit.iti.algover;

import java.util.ArrayList;
import java.util.List;

import edu.kit.iti.algover.parser.DafnyParser;
import edu.kit.iti.algover.parser.DafnyTree;


/**
 * The Class ProgramDatabase serves as database for all information on the
 * program: Defined functions, contracts, declared variables.
 *
 * At the moment, everything is parsed from the AST on demand.
 */
public class ProgramDatabase {

    private final DafnyTree program;

    public ProgramDatabase(DafnyTree program) {
        this.program = program;
    }

    public DafnyTree getMethod(String name) {
        for (DafnyTree f : program.getChildrenWithType(DafnyParser.METHOD)) {
            if(f.getChild(0).getText().equals(name)) {
                return f;
            }
        }
        return null;
    }

    /**
     * Retrieves all variable declarations from within a method declaration.
     * They may be arbitrarily nested.
     *
     * @param method
     *            the method to scan for declarations
     *
     * @return a freshly created, non-<code>null</code> list of var decls.
     */
    public static List<DafnyTree> getAllVariableDeclarations(DafnyTree method) {
        List<DafnyTree> allDeclarations = new ArrayList<DafnyTree>();
        collectVariableDeclarations(allDeclarations, method);
        return allDeclarations;
    }

    private static void collectVariableDeclarations(List<DafnyTree> collection, DafnyTree node) {
        if(node.getType() == DafnyParser.VAR) {
            collection.add(node);
        } else {
            // VARs are never nested.
            List<DafnyTree> children = node.getChildren();
            if(children != null) {
                for (DafnyTree child : children) {
                    collectVariableDeclarations(collection, child);
                }
            }
        }
    }

    public static List<DafnyTree> getArgumentDeclarations(DafnyTree method) {
        DafnyTree args = method.getFirstChildWithType(DafnyParser.ARGS);
        List<DafnyTree> allDeclarations = new ArrayList<DafnyTree>();
        collectVariableDeclarations(allDeclarations, args);
        return allDeclarations;
    }

    public static DafnyTree getVariableDeclaration(DafnyTree method, String name) {
        DafnyTree arg = getVariableDeclInList(method.getFirstChildWithType(DafnyParser.ARGS), name);
        if(arg != null) {
            return arg;
        }

        DafnyTree ret = getVariableDeclInList(method.getFirstChildWithType(DafnyParser.RETURNS), name);
        if(ret != null) {
            return ret;
        }

        DafnyTree var = getVariableDeclInList(method.getFirstChildWithType(DafnyParser.VAR), name);
        return var;
    }

    private static DafnyTree getVariableDeclInList(DafnyTree decls, String name) {
        if(decls != null) {
            for (DafnyTree decl : decls.getChildren()) {
                if(decl.getChild(0).getText().equals(name)) {
                    return decl;
                }
            }
        }
        return null;
    }

}
