package edu.kit.iti.algover.editor;

import org.antlr.runtime.Token;

import java.util.Collection;

public class LayeredHighlightingRule implements HighlightingRule {

    private final HighlightingRule[] layers;

    public LayeredHighlightingRule(int numLayers) {
        layers = new HighlightingRule[numLayers];
    }

    public void setLayer(int layer, HighlightingRule rule) {
        layers[layer] = rule;
    }

    @Override
    public Collection<String> handleToken(Token token, Collection<String> syntaxClasses) {
        Collection<String> classes = syntaxClasses;
        for (int i = 0; i < layers.length; i++) {
            if (layers[i] != null) {
                classes = layers[i].handleToken(token, classes);
            }
        }
        return classes;
    }
}
