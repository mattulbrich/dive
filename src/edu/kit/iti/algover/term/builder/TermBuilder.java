package edu.kit.iti.algover.term.builder;

import edu.kit.iti.algover.term.FunctionSymbol;
import edu.kit.iti.algover.term.Sort;

public class TermBuilder {

    public static final FunctionSymbol AND =
            new FunctionSymbol("$and", Sort.FORMULA, Sort.FORMULA, Sort.FORMULA);

    public static final FunctionSymbol OR =
            new FunctionSymbol("$or", Sort.FORMULA, Sort.FORMULA, Sort.FORMULA);

    public static final FunctionSymbol IMP =
            new FunctionSymbol("$imp", Sort.FORMULA, Sort.FORMULA, Sort.FORMULA);

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

}
