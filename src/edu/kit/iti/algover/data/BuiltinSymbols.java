/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2016 Karlsruhe Institute of Technology
 */

package edu.kit.iti.algover.data;

import java.lang.reflect.Field;
import java.lang.reflect.Modifier;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.List;

import edu.kit.iti.algover.term.FunctionSymbol;
import edu.kit.iti.algover.term.Sort;

/**
 * This class collects the builtin function symbols of the logic.
 *
 * By convention, names of builtin symbols have a leading $-sign to distinguish
 * them from user defined symbols.
 *
 * Some symbols are defined statically as constants, others are defined on
 * demand (since their number is unbounded in theory).
 *
 * @author Mattias Ulbrich
 */
public class BuiltinSymbols extends MapSymbolTable {

    public static final FunctionSymbol AND =
            new FunctionSymbol("$and", Sort.FORMULA, Sort.FORMULA, Sort.FORMULA);

    public static final FunctionSymbol OR =
            new FunctionSymbol("$or", Sort.FORMULA, Sort.FORMULA, Sort.FORMULA);

    public static final FunctionSymbol IMP =
            new FunctionSymbol("$imp", Sort.FORMULA, Sort.FORMULA, Sort.FORMULA);

    public static final FunctionSymbol NEG =
            new FunctionSymbol("$not", Sort.FORMULA, Sort.FORMULA);

    public static final FunctionSymbol GT =
            new FunctionSymbol("$gt", Sort.FORMULA, Sort.INT, Sort.INT);

    public static final FunctionSymbol GE =
            new FunctionSymbol("$ge", Sort.FORMULA, Sort.INT, Sort.INT);

    public static final FunctionSymbol LT =
            new FunctionSymbol("$lt", Sort.FORMULA, Sort.INT, Sort.INT);

    public static final FunctionSymbol LE =
            new FunctionSymbol("$le", Sort.FORMULA, Sort.INT, Sort.INT);

    public static final FunctionSymbol PLUS =
            new FunctionSymbol("$plus", Sort.INT, Sort.INT, Sort.INT);

    public static final FunctionSymbol TIMES =
            new FunctionSymbol("$times", Sort.INT, Sort.INT, Sort.INT);

    public static final FunctionSymbol UNION =
            new FunctionSymbol("$union", Sort.INT_SET, Sort.INT_SET, Sort.INT_SET);

    public static final FunctionSymbol INTERSECT =
            new FunctionSymbol("$intersect", Sort.INT_SET, Sort.INT_SET, Sort.INT_SET);

    public static final FunctionSymbol STORE1 =
            new FunctionSymbol("$store1", Sort.HEAP, Sort.HEAP, new Sort("array1"), Sort.INT, Sort.INT);

    public static final FunctionSymbol HEAP =
            new FunctionSymbol("$heap", Sort.HEAP);

    public BuiltinSymbols() {
        super(collectSymbols());
    }

    /**
     * This implementations resolves various special function symbols by name.
     */
    @Override
    protected FunctionSymbol resolve(String name) {

        //
        // type safe equality
        if(name.startsWith("$eq_")) {
            Sort sort = new Sort(name.substring(4));
            FunctionSymbol eq = new FunctionSymbol(name, Sort.FORMULA, Arrays.asList(sort, sort));
            return eq;
        }

        //
        // multidim length functions
        if(name.matches("\\$len[0-9]+")) {
            String suffix = name.substring(4);
            int dim = Integer.parseInt(suffix);
            Sort arraySort = new Sort("array" + (dim+1));
            FunctionSymbol len = new FunctionSymbol(name, Sort.INT, arraySort);
            return len;
        }

        //
        // non-negative integer literal
        if(name.matches("[0-9]+")) {
            FunctionSymbol lit = new FunctionSymbol(name, Sort.INT);
            return lit;
        }

        //
        // select of McCarthy's arrays (dimensional)
        if(name.matches("\\$select[0-9]+")) {
            String suffix = name.substring(7);
            int dim = Integer.parseInt(suffix);
            Sort arraySort = new Sort("array" + suffix);
            List<Sort> args = new ArrayList<>();
            args.add(Sort.HEAP);
            args.add(arraySort);
            args.addAll(Collections.nCopies(dim, Sort.INT));
            FunctionSymbol len = new FunctionSymbol(name, Sort.INT, args);
            return len;
        }

        // otherwise we cannot resolve that
        return null;
    }

    private static Collection<FunctionSymbol> collectSymbols() {
        List<FunctionSymbol> result = new ArrayList<>();
        for(Field f : BuiltinSymbols.class.getDeclaredFields()) {
            if(!Modifier.isStatic(f.getModifiers())) {
                continue;
            }
            if(f.getType() != FunctionSymbol.class) {
                continue;
            }

            FunctionSymbol fs;
            try {
                fs = (FunctionSymbol) f.get(null);
            } catch (IllegalAccessException e) {
                throw new Error(e);
            }

            result.add(fs);
        }

        return result;
    }
}
