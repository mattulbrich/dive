package edu.kit.iti.algover.browser.callvisualization;

import edu.kit.iti.algover.dafnystructures.Callgraph;
import edu.kit.iti.algover.dafnystructures.DafnyDecl;
import edu.kit.iti.algover.parser.DafnyTree;

import java.util.Collection;
import java.util.Collections;
import java.util.List;
import java.util.stream.Collectors;

public class CallVisualizationModel {

    private Callgraph graph;

    private DafnyDecl selectedDeclaration;

    private Collection<DafnyTree> calls;

    private Collection<DafnyTree> callSites;

    public CallVisualizationModel(Callgraph graph, DafnyDecl selectedDeclaration, Collection<DafnyTree> calls, Collection<DafnyTree> callSites) {
        this.graph = graph;
        this.selectedDeclaration = selectedDeclaration;
        this.calls = calls;
        this.callSites = callSites;
    }

    public DafnyDecl getDecl(DafnyTree tree){
        return graph.getDecl(tree);
    }

    public DafnyTree getDeclTree(DafnyTree tree){
        return graph.getDecl(tree).getRepresentation();
    }
    public Callgraph getGraph() {
        return graph;
    }

    public DafnyDecl getSelectedDeclaration() {
        return selectedDeclaration;
    }

    public Collection<DafnyTree> getCalls() {
        return calls;
    }

    public Collection<DafnyTree> getCallSites() {
        return callSites;
    }

}
