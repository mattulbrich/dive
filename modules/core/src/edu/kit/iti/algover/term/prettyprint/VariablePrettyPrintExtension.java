package edu.kit.iti.algover.term.prettyprint;

import edu.kit.iti.algover.term.VariableTerm;
import nonnull.NonNull;

public interface VariablePrettyPrintExtension {

    /**
     * Checks if this pretty print extension takes care of a particular name of a variable term.
     *
     * The extension must be able to print all applications of the function symbol.
     *
     * @param variable a non-<code>null</code> function symbol to check
     * @return true iff the extension han handle the argument.
     */
    boolean canPrint(@NonNull VariableTerm variable);

    /**
     * Do the actual pretty printing for a given application term.
     *
     * @param variable        the term to pretty print.
     * @param prettyPrintVisitor the visitor can be used for call backs for subterms.
     */
    void print(@NonNull VariableTerm variable, @NonNull PrettyPrintVisitor prettyPrintVisitor);
}
