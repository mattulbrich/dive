/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.parser;

/**
 * The Class ParameterContractionVisitor is part of the syntactic desugaring.
 *
 * It combines logic identifiers and their typeparameters into
 * single identifier nodes since they are used for lookup on the logic side.
 *
 * Parametrised non-logic identifiers need to be treated differently.
 *
 * @author mulbrich
 */
class ParameterContractionVisitor extends DafnyTreeDefaultVisitor<Void, Void> {

    /**
     * {@inheritDoc}
     *
     * Print the identifier and its parameters into a string builder. Replaces
     * the original text of the token, modifies its type to ID and removes the
     * children.
     */
    @Override
    public Void visitLOGIC_ID(DafnyTree t, Void a) {
        StringBuilder sb = new StringBuilder();
        contract(sb, t);
        t.getToken().setText(sb.toString());
        t.getToken().setType(DafnyParser.ID);
        t.removeAllChildren();
        return null;
    }

    /*
     * Prints the type parameters into the string builder.
     */
    private void contract(StringBuilder sb, DafnyTree t) {

        sb.append(t.getText());

        if(t.getChildCount() == 0) {
            return;
        }

        sb.append("<");
        boolean first = true;
        for (DafnyTree child : t.getChildren()) {
            if(first) {
                first = false;
            } else {
                sb.append(",");
            }
            contract(sb, child);
        }
        sb.append(">");
    }
}
