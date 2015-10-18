package edu.kit.iti.algover.data;

import java.lang.reflect.Field;
import java.lang.reflect.Modifier;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import edu.kit.iti.algover.term.FunctionSymbol;
import edu.kit.iti.algover.term.Sort;

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
            new FunctionSymbol("$gt", Sort.INT, Sort.INT, Sort.FORMULA);

    public static final FunctionSymbol GE =
            new FunctionSymbol("$ge", Sort.INT, Sort.INT, Sort.FORMULA);

    public static final FunctionSymbol LT =
            new FunctionSymbol("$lt", Sort.INT, Sort.INT, Sort.FORMULA);

    public static final FunctionSymbol LE =
            new FunctionSymbol("$le", Sort.INT, Sort.INT, Sort.FORMULA);

    public static final FunctionSymbol PLUS =
            new FunctionSymbol("$plus", Sort.INT, Sort.INT, Sort.INT);

    public static final FunctionSymbol TIMES =
            new FunctionSymbol("$times", Sort.INT, Sort.INT, Sort.INT);

    public static final FunctionSymbol UNION =
            new FunctionSymbol("$union", Sort.INT_SET, Sort.INT_SET, Sort.INT_SET);

    public static final FunctionSymbol INTERSECT =
            new FunctionSymbol("$intersect", Sort.INT_SET, Sort.INT_SET, Sort.INT_SET);

    public BuiltinSymbols() {
        super(collectSymbols());
    }

    @Override
    protected FunctionSymbol resolve(String name) {

        if(name.startsWith("$eq_")) {
            Sort sort = new Sort(name.substring(4));
            FunctionSymbol eq = new FunctionSymbol(name, Sort.FORMULA, Arrays.asList(sort, sort));
            return eq;
        }

        if(name.matches("\\$len[0-9]+")) {
            String suffix = name.substring(4);
            Sort arraySort = new Sort("array" + suffix);
            FunctionSymbol len = new FunctionSymbol(name, Sort.INT, Arrays.asList(arraySort));
            return len;
        }

        if(name.matches("[0-9]+")) {
            FunctionSymbol lit = new FunctionSymbol(name, Sort.INT);
            return lit;
        }

        if(name.matches("\\$select[0-9]+")) {
            String suffix = name.substring(7);
            int dim = Integer.parseInt(suffix);
            Sort arraySort = new Sort("array" + suffix);
            List<Sort> args = new ArrayList<>();
            args.add(arraySort);
            args.addAll(Collections.nCopies(dim, Sort.INT));
            FunctionSymbol len = new FunctionSymbol(name, Sort.INT, args);
            return len;
        }

        return null;
    }

    private static Map<String, FunctionSymbol> collectSymbols() {
        Map<String, FunctionSymbol> result = new HashMap<>();
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

            result.put(fs.getName(), fs);
        }

        return result;
    }
}
