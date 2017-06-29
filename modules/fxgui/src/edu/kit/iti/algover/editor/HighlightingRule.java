package edu.kit.iti.algover.editor;

import org.antlr.runtime.Token;

import java.util.Collection;

/**
 * Created by Philipp on 29.06.2017.
 */
@FunctionalInterface
public interface HighlightingRule {

    Collection<String> handleToken(Token token, Collection<String> syntaxClasses);

}
