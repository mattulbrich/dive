/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 *
 */

package edu.kit.iti.algover.dafnystructures;

import edu.kit.iti.algover.parser.DafnyParser;
import edu.kit.iti.algover.parser.DafnyTree;
import edu.kit.iti.algover.parser.DafnyTreeDefaultVisitor;
import edu.kit.iti.algover.project.Project;
import nonnull.NonNull;
import org.antlr.runtime.tree.Tree;

import java.util.ArrayList;
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
     * The assignment of the actual SCCs. Two declarations belong to the same
     * SCC iff they have the same value in this map.
     */
    private final Map<DafnyDecl, Integer> sccs = new IdentityHashMap<>();

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
     * Get a map that assigns to dafny declarations the SCC they belong to.
     * Two declarations are in the same SCC iff the are mapped to the same value in the resulting map.
     *
     * The result map contains sensible values only after calling {@link #computeSCCs()}.
     *
     * @return an immutable view to the scc map of the algorithm.
     */
    public @NonNull Map<DafnyDecl, Integer> getSCCs() {
        return Collections.unmodifiableMap(sccs);
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
        sccs.clear();

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
            do {
                w = stack.pop();
                sccs.put(w, curSCC);
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

    private Set<DafnyDecl> getCalledDecls(DafnyDecl decl) {
        Set<DafnyDecl> result = new HashSet<>();
        decl.getRepresentation().accept(new Visitor(), result);
        return result;
    }

    /*
     * This visitor allows one to find all referenced methods and functions
     * used within a mehtod/function body.
     */
    private class Visitor extends DafnyTreeDefaultVisitor<Void, Set<DafnyDecl>> {

        @Override
        public Void visitDefault(DafnyTree t, Set<DafnyDecl> arg) {
            for (DafnyTree child : t.getChildren()) {
                child.accept(this, arg);
            }
            return null;
        }

        @Override
        public Void visitCALL(DafnyTree t, Set<DafnyDecl> set) {

            DafnyTree declRef = t.getChild(0).getDeclarationReference();
            if(declRef != null) {
                int ty = declRef.getType();
                if (ty == DafnyParser.METHOD || ty == DafnyParser.FUNCTION) {
                    String name = declRef.getChild(0).getText();
                    Tree parent = declRef.getParent();
                    if (parent.getType() == DafnyParser.CLASS) {
                        DafnyClass clss = project.getClass(parent.getChild(0).getText());
                        if (ty == DafnyParser.METHOD) {
                            set.add(clss.getMethod(name));
                        } else {
                            set.add(clss.getFunction(name));
                        }
                    } else {
                        if (ty == DafnyParser.METHOD) {
                            set.add(project.getMethod(name));
                        } else {
                            set.add(project.getFunction(name));
                        }
                    }
                }
            }

            return super.visitCALL(t, set);
        }
    }
}
