package edu.kit.iti.algover.browser.callvisualization;

import edu.kit.iti.algover.dafnystructures.Callgraph;
import edu.kit.iti.algover.dafnystructures.DafnyDecl;
import edu.kit.iti.algover.parser.DafnyTree;

import java.util.Collection;

public class CallVisualizationModel {

    private Callgraph graph;

    private DafnyDecl selectedDeclaration;

    private Collection<DafnyTree> calls;

    private Collection<DafnyTree> callSites;
}
