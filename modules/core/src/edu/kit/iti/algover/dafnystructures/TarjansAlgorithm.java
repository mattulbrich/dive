/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.dafnystructures;

import edu.kit.iti.algover.parser.DafnyParser;
import edu.kit.iti.algover.parser.DafnyTree;
import edu.kit.iti.algover.parser.DafnyTreeDefaultVisitor;
import edu.kit.iti.algover.project.Project;
import nonnull.NonNull;
import org.antlr.runtime.tree.Tree;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.Stack;

/**
 * This algorithm is used to compute strongly connected components in the
 * callgraph of the project.
 *
 * They are used to determine if a variant needs to be regarded or whether
 * the call needs not check for termination.
 *
 * The analysis covers methods and function defintions and calls.
 *
 * Tarjan's algorithm is used which works with a single iteratio over the
 * nodes.
 *
 * For the algorithm, see also
 * https://en.wikipedia.org/wiki/Tarjan%27s_strongly_connected_components_algorithm.
 *
 * @author Mattias Ulbrich
 */
public class TarjansAlgorithm {

    /**
     * A constant identifier to be used as (artificial) type in
     * {@link DafnyTree}s.
     */
    public static final int CALLGRAPH_SCC = -2;

    /**
     * The project for which the computation takes place.
     */
    private final Project project;

    /**
     * The lowlink values used in the algorithm.
     */
    private final Map<DafnyDecl, Integer> lowlinks = new IdentityHashMap<>();

    /**
     * The index values used in the algorithm,
     */
    private final Map<DafnyDecl, Integer> indexes = new IdentityHashMap<>();

    /**
     * The stack "S" used within the algorithm
     */
    private final Stack<DafnyDecl> stack = new Stack<>();

    /**
     * the current index to make index assignment unique.
     */
    private int curIndex;

    /**
     * the current number of given SCCs to make SCC assignment unique.
     */
    private int curSCC;

    /**
     * Instantiate a new SCC algorithm.
     *
     * @param project the project to crawl.
     */
    public TarjansAlgorithm(@NonNull Project project) {
        this.project = project;
    }

    /**
     * initialise SCC computation.
     *
     * This clears all data structures used in this object.
     *
     * Caution: The results of previous computations is lost!
     */
    public void computeSCCs() {

        curIndex = 0;
        stack.clear();
        lowlinks.clear();
        indexes.clear();

        for (DafnyDecl decl : getAllCallableDecls()) {
            if (!indexes.containsKey(decl)) {
                compute(decl);
            }
        }

    }
    /*
     * Do Tarjan's algorithm.
     */
    private void compute(DafnyDecl decl) {

        // Set the depth index for v to the smallest unused index
        indexes.put(decl, curIndex);
        lowlinks.put(decl, curIndex);
        curIndex ++;
        stack.push(decl);

        // Consider successors of v
        for(DafnyDecl called : getCalledDecls(decl)) {
            if (!indexes.containsKey(called)) {
                // Successor w has not yet been visited; recurse on it
                compute(called);
                lowlinks.put(decl, Math.min(lowlinks.get(decl), lowlinks.get(called)));
            } else if (stack.contains(called)) {
                // check could be done O(1) but ...
                // Successor w is in stack S and hence in the current SCC
                // If w is not on stack, then (v, w) is a cross-edge in the DFS tree and must be ignored
                // Note: The next line may look odd - but is correct.
                // It says w.index not w.lowlink; that is deliberate and from the original paper
                lowlinks.put(decl, Math.min(lowlinks.get(decl), indexes.get(called)));
            }
        }

        // If v is a root node, pop the stack and generate an SCC
        if (lowlinks.get(decl) == indexes.get(decl)) {
            DafnyDecl w;
            DafnyTree sccTree = new DafnyTree(CALLGRAPH_SCC, "scc_" + curSCC);
            do {
                w = stack.pop();
                w.getRepresentation().setExpressionType(sccTree);
            } while (w != decl);

            curSCC++;
        }

    }

    /**
     * Get a list of all callable entities (methods and functions) defined in the project.
     *
     * This is needed for dependency analysis.
     *
     * @return a freshly created collection of a callable declarations.
     */
    private List<DafnyDecl> getAllCallableDecls() {
        List<DafnyDecl> result = new ArrayList<>();
        for (DafnyClass dafnyClass : project.getClasses()) {
            result.addAll(dafnyClass.getMethods());
            result.addAll(dafnyClass.getFunctions());
        }
        result.addAll(project.getMethods());
        result.addAll(project.getFunctions());

        return result;
    }

    /**
     * Find all declarations that are called from within decl.
     *
     * @param decl, a method or function declaration
     * @return all invoked method/function declarations
     */
    private Set<DafnyDecl> getCalledDecls(DafnyDecl decl) {

        Callgraph graph = project.getCallgraph();
        Collection<DafnyTree> calls = graph.getCalls(decl);

        Set<DafnyDecl> result = new HashSet<>();
        for (DafnyTree call : calls) {
            if (call.getChild(0).getDeclarationReference() != null) {
                // if name cannot be resolved the reference is null, ignore these
                result.add(graph.getDecl(call));
            }
        }
        return result;
    }

}
