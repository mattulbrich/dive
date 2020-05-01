/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.data;

import java.lang.reflect.Field;
import java.lang.reflect.Modifier;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import edu.kit.iti.algover.symbex.PathConditionElement;
import edu.kit.iti.algover.term.FunctionSymbol;
import edu.kit.iti.algover.term.FunctionSymbolFamily;
import edu.kit.iti.algover.term.Sort;
import edu.kit.iti.algover.util.Util;
import nonnull.DeepNonNull;
import nonnull.NonNull;
import nonnull.Nullable;

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

    public static final Sort ARRAY1 =
            Sort.get("array", FunctionSymbolFamily.VAR1);

    public static final Sort ARRAY2_1 =
            Sort.get("array2", FunctionSymbolFamily.VAR1);

    public static final FunctionSymbolFamily ARRAY_SELECT =
            new FunctionSymbolFamily(
                    new FunctionSymbol("$array_select", FunctionSymbolFamily.VAR1,
                            Sort.HEAP, ARRAY1, Sort.INT), 1);

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

    public static final FunctionSymbol DIV =
            new FunctionSymbol("$div", Sort.INT, Sort.INT, Sort.INT);

    public static final FunctionSymbol MODULO =
            new FunctionSymbol("$modulo", Sort.INT, Sort.INT, Sort.INT);


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
                            Sort.HEAP, ARRAY2_1,
                            Sort.INT, Sort.INT), 1);
    public static final FunctionSymbolFamily LEN =
            new FunctionSymbolFamily(
                    new FunctionSymbol("$len", Sort.INT,
                            ARRAY1), 1);
    public static final FunctionSymbolFamily LEN0 =
            new FunctionSymbolFamily(
                    new FunctionSymbol("$len0", Sort.INT,
                            ARRAY2_1), 1);
    public static final FunctionSymbolFamily LEN1 =
            new FunctionSymbolFamily(
                    new FunctionSymbol("$len1", Sort.INT,
                            ARRAY2_1), 1);
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
                            ARRAY1,
                            Sort.INT,
                            FunctionSymbolFamily.VAR1), 1);

    public static final FunctionSymbolFamily ARRAY2_STORE =
            new FunctionSymbolFamily(
                    new FunctionSymbol("$array2_store", Sort.HEAP,
                            Sort.HEAP,
                            ARRAY2_1,
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

    // Assignable variable for the modifies set
    public static final FunctionSymbol MOD =
            new FunctionSymbol("$mod", Sort.get("set", Sort.OBJECT));

    // Assignable variable for the decreases clause
    // TODO Go beyond integers here one day.
    public static final FunctionSymbol DECR =
            new FunctionSymbol("$decr", Sort.INT);

    private static final Sort SET1 = Sort.get("set", FunctionSymbolFamily.VAR1);

    public static final FunctionSymbolFamily UNION =
            new FunctionSymbolFamily(
                    new FunctionSymbol("$union", SET1, SET1, SET1), 1);

    public static final FunctionSymbolFamily INTERSECT =
            new FunctionSymbolFamily(
                    new FunctionSymbol("$intersect", SET1, SET1, SET1), 1);

    public static final FunctionSymbolFamily SET_MINUS =
            new FunctionSymbolFamily(
                    new FunctionSymbol("$set_minus", SET1, SET1, SET1), 1);

    public static final FunctionSymbol EMPTY_SET =
            new FunctionSymbol("$empty", Sort.get("set", Sort.BOTTOM));

    public static final FunctionSymbolFamily CARD =
            new FunctionSymbolFamily(
                    new FunctionSymbol("$set_card", Sort.INT, SET1), 1);

    public static final FunctionSymbolFamily SET_ADD =
            new FunctionSymbolFamily(
                    new FunctionSymbol("$set_add", SET1, FunctionSymbolFamily.VAR1, SET1), 1);

    public static final FunctionSymbolFamily SET_IN =
            new FunctionSymbolFamily(
                    new FunctionSymbol("$set_in", Sort.BOOL, FunctionSymbolFamily.VAR1, SET1), 1);

    public static final FunctionSymbolFamily SUBSET =
            new FunctionSymbolFamily(
                    new FunctionSymbol("$subset", Sort.BOOL, SET1, SET1), 1);


    private static final Sort SEQ1 = Sort.get("seq", FunctionSymbolFamily.VAR1);

    public static final FunctionSymbolFamily SEQ_LEN =
            new FunctionSymbolFamily(
                    new FunctionSymbol("$seq_len", Sort.INT, SEQ1), 1);

    public static final FunctionSymbolFamily SEQ_GET =
            new FunctionSymbolFamily(
                    new FunctionSymbol("$seq_get", FunctionSymbolFamily.VAR1,
                            SEQ1, Sort.INT), 1);

    public static final FunctionSymbolFamily SEQ_UPDATE =
            new FunctionSymbolFamily(
                    new FunctionSymbol("$seq_upd", SEQ1,
                            SEQ1, Sort.INT, FunctionSymbolFamily.VAR1), 1);

    public static final FunctionSymbol SEQ_EMPTY =
            new FunctionSymbol("$seq_empty", Sort.get("seq", Sort.BOTTOM));

    public static final FunctionSymbolFamily SEQ_CONS =
            new FunctionSymbolFamily(
                    new FunctionSymbol("$seq_cons", SEQ1, FunctionSymbolFamily.VAR1, SEQ1), 1);

    public static final FunctionSymbolFamily SEQ_CONCAT =
            new FunctionSymbolFamily(
                    new FunctionSymbol("$seq_concat", SEQ1, SEQ1, SEQ1), 1);

    public static final FunctionSymbolFamily SEQ_SUB =
            new FunctionSymbolFamily(
                    new FunctionSymbol("$seq_sub", SEQ1, SEQ1, Sort.INT, Sort.INT), 1);

    public static final FunctionSymbolFamily ARRAY_TO_SEQ =
            new FunctionSymbolFamily(
                    new FunctionSymbol("$array2seq", SEQ1, Sort.HEAP, ARRAY1),1);

    private static final Sort SET_OBJECTS = Sort.get("set", Sort.OBJECT);

    public static final FunctionSymbol EVERYTHING =
            new FunctionSymbol("$everything", SET_OBJECTS);

    public static final FunctionSymbol ANON =
            new FunctionSymbol("$anon", Sort.HEAP, Sort.HEAP, SET_OBJECTS, Sort.HEAP);

    public static final FunctionSymbol CREATE =
            new FunctionSymbol("$create", Sort.HEAP, Sort.HEAP, Sort.OBJECT);

    public static final FunctionSymbol IS_CREATED =
            new FunctionSymbol("$isCreated", Sort.BOOL, Sort.HEAP, Sort.OBJECT);

    public static final FunctionSymbol FRESH_OBJECTS =
            new FunctionSymbol("$freshObjects", SET_OBJECTS, Sort.HEAP);


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
    protected @Nullable FunctionSymbol resolve(@NonNull String name, @DeepNonNull List<Sort> argSorts) {

        if (argSorts.isEmpty()) {
            int index = name.indexOf("<");
            if (index >= 0) {
                argSorts = FunctionSymbolFamily.parseSortParameters(name);
                name = name.substring(0, index);
            }
        }

        if (!argSorts.isEmpty()) {
            FunctionSymbolFamily family = symbolFamilies.get(name);
            if(family != null) {
                return family.instantiate(argSorts);
            } else {
                return null;
            }
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
