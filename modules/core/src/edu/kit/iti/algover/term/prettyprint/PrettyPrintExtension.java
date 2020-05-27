/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.term.prettyprint;

import edu.kit.iti.algover.term.ApplTerm;
import edu.kit.iti.algover.term.FunctionSymbol;
import nonnull.NonNull;

public interface PrettyPrintExtension {

    /**
     * Checks if this pretty print extension takes care of a particular function symbol.
     *
     * The extension must be able to print all applications of the function symbol.
     *
     * @param functionSymbol a non-<code>null</code> function symbol to check
     * @return true iff the extension han handle the argument.
     */
    boolean canPrint(@NonNull FunctionSymbol functionSymbol);

    /**
     * Get the precedence of the first infix/postfix/mixfix operator in the resulting
     * expression.
     *
     * This is used to decide whether or not parentheses must be added around the expression.
     *
     * For expressions that bind strongest (e.g. postfix suffixes), the value should be 1000.
     *
     * @param application the term for which the precedence is to be given
     * @return {@code 0 <= result <= 1000}
     */
    int getLeftPrecedence(ApplTerm application);

    /**
     * Get the precedence of the las infix/prefix/mixfix operator in the resulting
     * expression.
     *
     * This is used to decide whether or not parentheses must be added around the expression.
     *
     * For expressions that bind strongest (e.g. postfix suffixes), the value should be 1000.
     *
     * @param application the term for which the precedence is to be given
     * @return {@code 0 <= result <= 1000}
     */
    int getRightPrecedence(ApplTerm application);

    /**
     * Do the actual pretty printing for a given application term.
     *
     * @param application        the term to pretty print.
     * @param prettyPrintVisitor the visitor can be used for call backs for subterms.
     */
    void print(@NonNull ApplTerm application, @NonNull PrettyPrintVisitor prettyPrintVisitor);

}
