package edu.kit.iti.algover.util;

import org.antlr.runtime.CommonToken;

import edu.kit.iti.algover.parser.DafnyParser;
import edu.kit.iti.algover.parser.DafnyTree;

public class ASTUtil {

    private ASTUtil() {
        throw new Error();
    }

    /**
     * Create an AST for the negation of a formula
     *
     * @param cond the AST for a formula
     * @return the AST for the negated formula.
     */
    public static DafnyTree negate(DafnyTree cond) {
        DafnyTree result= new DafnyTree(new CommonToken(DafnyParser.NOT, "not"));
        result.addChild(cond);
        return result;
    }

}
