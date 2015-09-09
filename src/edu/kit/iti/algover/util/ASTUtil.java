package edu.kit.iti.algover.util;

import org.antlr.runtime.CommonToken;

import edu.kit.iti.algover.parser.PseudoParser;
import edu.kit.iti.algover.parser.PseudoTree;

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
    public static PseudoTree negate(PseudoTree cond) {
        PseudoTree result= new PseudoTree(new CommonToken(PseudoParser.NOT, "not"));
        result.addChild(cond);
        return result;
    }

}
