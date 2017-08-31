/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.smt;

import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.InputStream;
import java.util.ArrayList;
import java.util.List;
import java.util.Properties;

import edu.kit.iti.algover.term.ApplTerm;
import edu.kit.iti.algover.term.DefaultTermVisitor;
import edu.kit.iti.algover.term.FunctionSymbol;
import edu.kit.iti.algover.term.FunctionSymbolFamily.InstantiatedFunctionSymbol;
import edu.kit.iti.algover.term.LetTerm;
import edu.kit.iti.algover.term.QuantTerm;
import edu.kit.iti.algover.term.SchemaVarTerm;
import edu.kit.iti.algover.term.Sort;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.term.TermVisitor;
import edu.kit.iti.algover.term.VariableTerm;
import edu.kit.iti.algover.util.Pair;

/**
 * Translation of formulas/terms into SMT source code.
 *
 * This class is a {@link TermVisitor} that mainly does syntactical
 * translations. The table {@link #OP_MAP} is kept as lookup table for symbol
 * names.
 *
 * SMT expressions are modelled using simple expressions ({@link SExpr}).
 *
 * TODO Length of arrays is not yet implemented.
 *
 * @author Mattias Ulbrich
 */

public class SMTTrans extends DefaultTermVisitor<Void, SExpr, RuntimeException> {

    /**
     * A map which keeps smt translations for builtin function symbols.
     */
    private static Properties OP_MAP;
    static {
        OP_MAP = new Properties();
        try(InputStream fis = SMTTrans.class.getResourceAsStream("opnames.txt")) {
            if(fis == null) {
                throw new FileNotFoundException("opnames.txt");
            }
            OP_MAP.load(fis);
        } catch (IOException e) {
            throw new Error(e);
        }
    }

    /**
     * Translate a formula into smt.
     *
     * @param formula
     *            the non-<code>null</code> formula (term of type
     *            {@link Sort#FORMULA}) to be translated
     * @return an s-expression capturing the SMT translation.
     */
    public SExpr trans(Term formula) {
        return formula.accept(this, null);
    }

    @Override
    protected SExpr defaultVisit(Term term, Void arg) {
        throw new Error("Missing method for " + term.getClass());
    }

    // That is fine for now. ... Later redefinition is expected
    public static SExpr typeToSMT(Sort sort) {

        String name = sort.getName();
        if (name.matches("array[0-9]+")) {
            int dim = Integer.parseInt(name.substring(5));
            assert dim == 1 : "For the moment we are limited";
            return new SExpr("Ref");
        } else {
            switch (name) {
                case "int":
                    return new SExpr("Int");
                case "set":
                    return new SExpr("Array", "Int", "Boolean");
                case "bool":
                    return new SExpr("Bool");
                case "null":
                    return new SExpr("object");
            }
        }
        throw new UnsupportedOperationException("Unsupported sort: " + sort);
    }

    @Override
    public SExpr visit(QuantTerm term, Void arg) {

        String quantifier;
        switch (term.getQuantifier()) {
        case EXISTS:
            quantifier = "exists";
            break;
        case FORALL:
            quantifier = "forall";
            break;
        default:
            throw new UnsupportedOperationException("Unknown quantifier: " + term);
        }

        VariableTerm boundVar = term.getBoundVar();
        SExpr sort = typeToSMT(boundVar.getSort());
        SExpr qvar = new SExpr(boundVar.getName(), sort);
        SExpr qqvar = new SExpr(qvar);

        SExpr formula = term.getTerm(0).accept(this, null);

        return new SExpr(quantifier, qqvar, formula);
    }

    @Override
    public SExpr visit(SchemaVarTerm term, Void arg) {
        throw new UnsupportedOperationException("Schema variables are not supported for SMT solving");
    }

    @Override
    public SExpr visit(VariableTerm term, Void arg) {
        return new SExpr(term.getName());
    }

    @Override
    public SExpr visit(LetTerm letTerm, Void arg) {
        SExpr inner = letTerm.getTerm(0).accept(this, null);
        List<SExpr> substitutions = new ArrayList<SExpr>();
        for (Pair<VariableTerm, Term> pair : letTerm.getSubstitutions()) {
            substitutions.add(new SExpr(pair.fst.getName(), pair.snd.accept(this, null)));
        }
        return new SExpr("let", new SExpr(substitutions), inner);
    }

    @Override
    public SExpr visit(ApplTerm term, Void arg) {

        FunctionSymbol f = term.getFunctionSymbol();
        String name = f.getName();
        if (OP_MAP.containsKey(name)) {
            name = OP_MAP.getProperty(name);
        } else if (f instanceof InstantiatedFunctionSymbol) {
            InstantiatedFunctionSymbol ifs = (InstantiatedFunctionSymbol) f;
            String basename = ifs.getFamily().getBaseName();
            if (OP_MAP.containsKey(basename)) {
                name = OP_MAP.getProperty(basename);
            }
        }

        List<SExpr> children = new ArrayList<>();
        for (Term subterm : term.getSubterms()) {
            children.add(subterm.accept(this, null));
        }

        return new SExpr(name, children);
    }

}
