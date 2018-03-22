/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
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
     * @param application
     * @return
     */
    int getLeftPrecedence(ApplTerm application);

    /**
     * Get the precedence of the las infix/prefix/mixfix operator in the resulting
     * expression.
     *
     * This is used to decide whether or not parentheses must be added around the expression.
     * @param application
     * @return
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
