package edu.kit.iti.algover.editor;

import org.antlr.runtime.Token;

import java.util.Collection;

/**
 * This can be used to compute additional highlighting on top of the standard
 * dafny code syntax highlighting in {@link DafnyCodeArea}s.
 * <p>
 * For a simple example, see {@link ReferenceHighlightingRule}.
 * <p>
 * Created by Philipp on 29.06.2017.
 */
@FunctionalInterface
public interface HighlightingRule {

    /**
     * 'Override' the previously computed syntax classes on the given token by
     * returing a new collection of syntax classes.
     *
     * @param token         the token to be styled
     * @param syntaxClasses the syntax classes that would be applied if this HighlightingRule
     *                      were not set in the DafnyCodeArea
     * @return a new collection of syntax classes to use instead of the given ones
     */
    Collection<String> handleToken(Token token, Collection<String> syntaxClasses);

}
