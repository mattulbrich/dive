package edu.kit.iti.algover.browser.callvisualization;

import org.antlr.runtime.Token;

public interface HighlightingHandler {

    void onRequestHighlight(String filename, Token startToken, Token stopToken);

}
