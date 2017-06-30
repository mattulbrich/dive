/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
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
 * @author mulbrich
 */
public class LabelIntroducer extends DafnyTreeDefaultVisitor<Void, Void>{

    public LabelIntroducer() {
    }

    private Set<String> takenLabels = new HashSet<>();
    private Map<Token, String> insertions = new IdentityHashMap<>();

    public void dumpWithInsertions(List<? extends Token> tokens, Appendable stream) throws IOException {
        for (Token token : tokens) {
            if(token.getType() != DafnyParser.EOF) {
                stream.append(token.getText());
                String label = insertions.get(token);
                if(label != null) {
                    stream.append(" label ").append(label).append(":");
                }
            }
        }
    }

    @Override
    public Void visitDefault(DafnyTree t, Void arg) {
        for (DafnyTree child : t.getChildren()) {
            child.accept(this, null);
        }
        return null;
    }

    @Override
    public Void visitMETHOD(DafnyTree tree, Void a) {
        takenLabels.clear();
        collectTakenLabels(tree);
        visitDefault(tree, a);
        return null;
    }

    @Override
    public Void visitASSERT(DafnyTree tree, Void a) {
       addLabelIfNeeded("ass_", tree);
       return null;
    }

    @Override
    public Void visitINVARIANT(DafnyTree tree, Void a) {
        addLabelIfNeeded("inv_", tree);
        return null;
    }

    @Override
    public Void visitREQUIRES(DafnyTree tree, Void a) {
        addLabelIfNeeded("req_", tree);
        return null;
    }

    @Override
    public Void visitENSURES(DafnyTree tree, Void a) {
        addLabelIfNeeded("ens_", tree);
        return null;
    }

    private void collectTakenLabels(DafnyTree tree) {
        if(tree.getType() == DafnyParser.LABEL) {
            takenLabels.add(tree.getChild(0).getText());
        }
        for (DafnyTree child : tree.getChildren()) {
            collectTakenLabels(child);
        }
    }

    private String makeLabel(String prefix) {
        int i = 1;
        while(true) {
            String candidate = prefix + i;
            if(!takenLabels.contains(candidate)) {
                takenLabels.add(candidate);
                return candidate;
            }
            i++;
        }
    }

    private void addLabelIfNeeded(String prefix, DafnyTree tree) {
        DafnyTree label = tree.getFirstChildWithType(DafnyParser.LABEL);
        if(label == null) {
            String newlabel = makeLabel(prefix);
            DafnyTree idTree = new DafnyTree(DafnyParser.ID, newlabel);
            DafnyTree labelTree = new DafnyTree(DafnyParser.LABEL);
            labelTree.addChild(idTree);
            tree.insertChild(0, labelTree);
            insertions.put(tree.getToken(), newlabel);
        }
    }

}
