package edu.kit.iti.algover.rule.script;

import edu.kit.iti.algover.editor.HighlightingRule;
import org.antlr.runtime.Token;

import java.util.Collection;

public class LayeredHighlightingRulev4 implements HighlightingRulev4 {

    private final HighlightingRulev4[] layers;

    public LayeredHighlightingRulev4(int numLayers) {
        layers = new HighlightingRulev4[numLayers];
    }

    public void setLayer(int layer, HighlightingRulev4 rule) {
        layers[layer] = rule;
    }

    @Override
    public Collection<String> handleToken(org.antlr.v4.runtime.Token token, Collection<String> syntaxClasses) {
        Collection<String> classes = syntaxClasses;
        for (int i = 0; i < layers.length; i++) {
            if (layers[i] != null) {
                classes = layers[i].handleToken(token, classes);
            }
        }
        return classes;
    }
}
