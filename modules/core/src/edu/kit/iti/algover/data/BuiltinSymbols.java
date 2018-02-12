/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */

package edu.kit.iti.algover.data;

import java.lang.reflect.Field;
import java.lang.reflect.Modifier;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import edu.kit.iti.algover.term.FunctionSymbol;
import edu.kit.iti.algover.term.FunctionSymbolFamily;
import edu.kit.iti.algover.term.Sort;
import edu.kit.iti.algover.util.Util;

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

    public static final FunctionSymbolFamily ARRAY_SELECT =
            new FunctionSymbolFamily(
                    new FunctionSymbol("$array_select", FunctionSymbolFamily.VAR1,
                            Sort.HEAP, Sort.get("array", FunctionSymbolFamily.VAR1),
                            Sort.INT), 1);

    // Checkstyle: OFF JavadocVariableCheck

    public static final FunctionSymbol AND =
            new FunctionSymbol("$and", Sort.BOOL, Sort.BOOL, Sort.BOOL);

    public static final FunctionSymbol OR =
            new FunctionSymbol("$or", Sort.BOOL, Sort.BOOL, Sort.BOOL);

    public static final FunctionSymbol IMP =
            new FunctionSymbol("$imp", Sort.BOOL, Sort.BOOL, Sort.BOOL);

    public static final FunctionSymbol NOT =
            new FunctionSymbol("$not", Sort.BOOL, Sort.BOOL);

    public static final FunctionSymbol GT =
            new FunctionSymbol("$gt", Sort.BOOL, Sort.INT, Sort.INT);

    public static final FunctionSymbol GE =
            new FunctionSymbol("$ge", Sort.BOOL, Sort.INT, Sort.INT);

    public static final FunctionSymbol LT =
            new FunctionSymbol("$lt", Sort.BOOL, Sort.INT, Sort.INT);

    public static final FunctionSymbol LE =
            new FunctionSymbol("$le", Sort.BOOL, Sort.INT, Sort.INT);

    public static final FunctionSymbol PLUS =
            new FunctionSymbol("$plus", Sort.INT, Sort.INT, Sort.INT);

    public static final FunctionSymbol MINUS =
            new FunctionSymbol("$minus", Sort.INT, Sort.INT, Sort.INT);

    public static final FunctionSymbol NEG =
            new FunctionSymbol("$neg", Sort.INT, Sort.INT);

    public static final FunctionSymbol TIMES =
            new FunctionSymbol("$times", Sort.INT, Sort.INT, Sort.INT);

    public static final FunctionSymbolFamily ITE =
            new FunctionSymbolFamily(
                    new FunctionSymbol("$ite",
                            FunctionSymbolFamily.VAR1,
                            Sort.BOOL,
                            FunctionSymbolFamily.VAR1,
                            FunctionSymbolFamily.VAR1), 1);
    public static final FunctionSymbolFamily ARRAY2_SELECT =
            new FunctionSymbolFamily(
                    new FunctionSymbol("$array2_select", FunctionSymbolFamily.VAR1,
                            Sort.HEAP, Sort.get("array2", FunctionSymbolFamily.VAR1),
                            Sort.INT, Sort.INT), 1);
    public static final FunctionSymbolFamily LEN =
            new FunctionSymbolFamily(
                    new FunctionSymbol("$len", Sort.INT,
                            Sort.get("array", FunctionSymbolFamily.VAR1)), 1);
    public static final FunctionSymbolFamily LEN0 =
            new FunctionSymbolFamily(
                    new FunctionSymbol("$len0", Sort.INT,
                            Sort.get("array2", FunctionSymbolFamily.VAR1)), 1);
    public static final FunctionSymbolFamily LEN1 =
            new FunctionSymbolFamily(
                    new FunctionSymbol("$len1", Sort.INT,
                            Sort.get("array2", FunctionSymbolFamily.VAR1)), 1);
    public static final FunctionSymbol NULL =
            new FunctionSymbol("null", Sort.NULL);

    public static final FunctionSymbolFamily STORE =
            new FunctionSymbolFamily(
                    new FunctionSymbol("$store", Sort.HEAP,
                            Sort.HEAP,
                            FunctionSymbolFamily.VAR1,
                            Sort.get("field",
                                    FunctionSymbolFamily.VAR1,
                                    FunctionSymbolFamily.VAR2),
                            FunctionSymbolFamily.VAR2), 2);

    public static final FunctionSymbolFamily ARRAY_STORE =
            new FunctionSymbolFamily(
                    new FunctionSymbol("$array_store", Sort.HEAP,
                            Sort.HEAP,
                            Sort.get("array", FunctionSymbolFamily.VAR1),
                            Sort.INT,
                            FunctionSymbolFamily.VAR1), 1);

    public static final FunctionSymbolFamily ARRAY2_STORE =
            new FunctionSymbolFamily(
                    new FunctionSymbol("$array2_store", Sort.HEAP,
                            Sort.HEAP,
                            Sort.get("array", FunctionSymbolFamily.VAR1),
                            Sort.INT,
                            Sort.INT,
                            FunctionSymbolFamily.VAR1), 1);

    public static final FunctionSymbolFamily SELECT =
            new FunctionSymbolFamily(
                    new FunctionSymbol("$select", FunctionSymbolFamily.VAR2,
                            Sort.HEAP, FunctionSymbolFamily.VAR1,
                            Sort.get("field",
                                    FunctionSymbolFamily.VAR1,
                                    FunctionSymbolFamily.VAR2)), 2);

    public static final FunctionSymbol TRUE =
            new FunctionSymbol("true", Sort.BOOL);

    public static final FunctionSymbol FALSE =
            new FunctionSymbol("false", Sort.BOOL);

    public static final FunctionSymbolFamily EQ =
            new FunctionSymbolFamily(
                    new FunctionSymbol("$eq", Sort.BOOL,
                            FunctionSymbolFamily.VAR1, FunctionSymbolFamily.VAR1), 1);

    public static final FunctionSymbol HEAP =
            new FunctionSymbol("$heap", Sort.HEAP);

    public static final FunctionSymbol MOD =
            new FunctionSymbol("$mod", Sort.get("set", Sort.OBJECT));

    private static final Sort SET1 = Sort.get("set", FunctionSymbolFamily.VAR1);

    public static final FunctionSymbolFamily UNION =
            new FunctionSymbolFamily(
                    new FunctionSymbol("$union", SET1, SET1, SET1), 1);

    public static final FunctionSymbolFamily INTERSECT =
            new FunctionSymbolFamily(
                    new FunctionSymbol("$intersect", SET1, SET1, SET1), 1);

    private static final Sort SEQ1 = Sort.get("seq", FunctionSymbolFamily.VAR1);

    public static final FunctionSymbolFamily SEQ_LEN =
            new FunctionSymbolFamily(
                    new FunctionSymbol("$seq_len", Sort.INT, SEQ1), 1);

    public static final FunctionSymbolFamily SEQ_GET =
            new FunctionSymbolFamily(
                    new FunctionSymbol("$seq_get", FunctionSymbolFamily.VAR1,
                            SEQ1, Sort.INT), 1);

    private static final Sort SET_OBJECTS = Sort.get("set", Sort.OBJECT);

    public static final FunctionSymbol EVERYTHING =
            new FunctionSymbol("$everything", SET_OBJECTS);

    public static final FunctionSymbol ANON =
            new FunctionSymbol("$anon", Sort.HEAP, Sort.HEAP, SET_OBJECTS, Sort.HEAP);

    public static final FunctionSymbol CREATE =
            new FunctionSymbol("$create", Sort.HEAP, Sort.HEAP, Sort.OBJECT);

    // Checkstyle: ON JavadocVariableCheck
    private final Map<String, FunctionSymbolFamily> symbolFamilies =
            new HashMap<>();


    public BuiltinSymbols() {
        super(collectSymbols());
        collectFamilies();
    }

    /**
     * {@inheritDoc}
     *
     * <p>
     * This implementations resolves various special function symbols by name.
     * </p>
     *
     */
    @Override
    protected FunctionSymbol resolve(String name) {

        int index = name.indexOf("<");
        if (index >= 0) {

            String baseName = name.substring(0, index);
            FunctionSymbolFamily family = symbolFamilies.get(baseName);
            if (family == null) {
                return null;
            }

            assert name.endsWith(">");
            List<Sort> params = FunctionSymbolFamily.parseSortParameters(name);
            return family.instantiate(params);

        }

        //
        // non-negative integer literal
        if (name.matches("[0-9]+")) {
            FunctionSymbol lit = new FunctionSymbol(name, Sort.INT);
            return lit;
        }

        //
        // otherwise we cannot resolve that
        return null;
    }

    private static Collection<FunctionSymbol> collectSymbols() {
        List<FunctionSymbol> result = new ArrayList<>();
        for (Field f : BuiltinSymbols.class.getDeclaredFields()) {
            if (!Modifier.isStatic(f.getModifiers())) {
                continue;
            }
            if (f.getType() != FunctionSymbol.class) {
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

    private void collectFamilies() {
        for (Field f : BuiltinSymbols.class.getDeclaredFields()) {
            if (!Modifier.isStatic(f.getModifiers())) {
                continue;
            }
            if (f.getType() != FunctionSymbolFamily.class) {
                continue;
            }

            try {
                FunctionSymbolFamily family = (FunctionSymbolFamily) f.get(null);
                symbolFamilies.put(family.getBaseName(), family);
            } catch (IllegalAccessException e) {
                throw new Error(e);
            }

        }
    }
}
