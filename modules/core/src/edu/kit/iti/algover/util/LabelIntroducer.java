/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.util;

import java.io.IOException;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.antlr.runtime.Token;

import edu.kit.iti.algover.parser.DafnyParser;
import edu.kit.iti.algover.parser.DafnyTree;
import edu.kit.iti.algover.parser.DafnyTreeDefaultVisitor;

/**
 * This class can be used to add labels to invariants and postconditions which
 * are not named.
 *
 * Labels are added to all unlabelled requires, ensures, assert, invariant
 * annotations.
 *
 * If the original token stream is available, this class allows AFTER VISITATION
 * to dump the token stream with updated explicit labels. Thus the implicit labels
 * can be made explicit.
 *
 * @author mulbrich
 */
public class LabelIntroducer extends DafnyTreeDefaultVisitor<Void, Void> {

    /**
     * The set of label which are used in the currently visited method.
     */
    private Set<String> takenLabels = new HashSet<>();

    /**
     * Insertions to be made into the token stream (i.e. the source code).
     *
     * It is organised such that the keyword token (e.g. ENSURES) is the key
     * into the map. The value is the name of the introduced explicit label. For
     * insertion, after the keyword ("ensures"), the string " label
     * &lt;name&gt;:" is added.
     */
    private Map<Token, String> insertions = new IdentityHashMap<>();

    /**
     * Instantiates a new label introducing visitor.
     */
    public LabelIntroducer() {
    }

    /**
     * Dump a token list with inserted explicit labels.
     *
     * The labels which have been added to the AST in an earlier visitation can
     * be persisted by writing them to the source file.
     *
     * This only makes sense after a file has been visited.
     *
     * @param tokens
     *            the list of tokens, must be the SAME as the one used for
     *            parsing the file
     * @param stream
     *            the stream to which the output should be written
     * @throws IOException
     *             Signals that an I/O exception has occurred.
     */
    public void dumpWithInsertions(List<? extends Token> tokens, Appendable stream)
                throws IOException {
        for (Token token : tokens) {
            if (token.getType() != DafnyParser.EOF) {
                stream.append(token.getText());
                String label = insertions.get(token);
                if (label != null) {
                    stream.append(" label ").append(label).append(":");
                }
            }
        }
    }

    /*
     * Depth-first visitation
     */
    @Override
    public Void visitDefault(DafnyTree t, Void arg) {
        for (DafnyTree child : t.getChildren()) {
            child.accept(this, null);
        }
        return null;
    }

    /*
     * clear the cache of taken methods. collect all defined labels.
     * visit recursively.
     */
    @Override
    public Void visitMETHOD(DafnyTree tree, Void a) {
        takenLabels.clear();
        collectTakenLabels(tree);
        visitDefault(tree, a);
        return null;
    }

    /*
     * add a label if needed. Prefix is "ass_"
     */
    @Override
    public Void visitASSERT(DafnyTree tree, Void a) {
        addLabelIfNeeded("ass_", tree);
        return null;
    }

    /*
     * add a label if needed. Prefix is "inv_"
     */
    @Override
    public Void visitINVARIANT(DafnyTree tree, Void a) {
        addLabelIfNeeded("inv_", tree);
        return null;
    }

    /*
     * add a label if needed. Prefix is "req_"
     */
    @Override
    public Void visitREQUIRES(DafnyTree tree, Void a) {
        addLabelIfNeeded("req_", tree);
        return null;
    }

    /*
     * add a label if needed. Prefix is "ens_"
     */
    @Override
    public Void visitENSURES(DafnyTree tree, Void a) {
        addLabelIfNeeded("ens_", tree);
        return null;
    }

    /*
     * collect all identifiers used as label below tree. Does not matter
     * what the type of the labelled statement is.
     */
    private void collectTakenLabels(DafnyTree tree) {
        if (tree.getType() == DafnyParser.LABEL) {
            takenLabels.add(tree.getChild(0).getText());
        }
        for (DafnyTree child : tree.getChildren()) {
            collectTakenLabels(child);
        }
    }

    /*
     * create a new label which is not used in the method yet.
     */
    private String makeLabel(String prefix) {
        int i = 1;
        while (true) {
            String candidate = prefix + i;
            if (!takenLabels.contains(candidate)) {
                takenLabels.add(candidate);
                return candidate;
            }
            i++;
        }
    }

    private void addLabelIfNeeded(String prefix, DafnyTree tree) {
        DafnyTree label = tree.getFirstChildWithType(DafnyParser.LABEL);
        if (label == null) {
            String newlabel = makeLabel(prefix);
            DafnyTree idTree = new DafnyTree(DafnyParser.ID, newlabel);
            DafnyTree labelTree = new DafnyTree(DafnyParser.LABEL);
            labelTree.addChild(idTree);
            tree.insertChild(0, labelTree);
            insertions.put(tree.getToken(), newlabel);
        }
    }

}
