/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.smt;

import static edu.kit.iti.algover.smt.SExpr.Type.BOOL;
import static edu.kit.iti.algover.smt.SExpr.Type.HEAP;
import static edu.kit.iti.algover.smt.SExpr.Type.INT;
import static edu.kit.iti.algover.smt.SExpr.Type.UNIVERSE;

import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

import edu.kit.iti.algover.smt.SExpr.Type;
import edu.kit.iti.algover.smt.SMTOperatorMap.OperatorEntry;
import edu.kit.iti.algover.smt.SMTOperatorMap.SMTExporter;
import edu.kit.iti.algover.term.ApplTerm;
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
import edu.kit.iti.algover.util.Util;
import nonnull.NonNull;

/**
 * Translation of formulas/terms into SMT source code.
 *
 * This class is a {@link TermVisitor} that mainly does syntactical
 * translations. The table {@link #OP_MAP} is kept as lookup table for symbol
 * names and signatures.
 *
 * SMT expressions are modelled using simple expressions ({@link SExpr}).
 *
 * @author Mattias Ulbrich
 */

public class SMTTrans implements TermVisitor<Type, SExpr, SMTException> {

    /**
     * A map which keeps smt translations for builtin function symbols.
     */
    private static final SMTOperatorMap OP_MAP;
    static {
        try {
            OP_MAP = SMTOperatorMap.deserialize(
                    SMTTrans.class.getResource("opnames.xml"));
        } catch (IOException e) {
            // This is an internal error which should never ever happen.
            // We cannot continue without the map. Raise an error.
            throw new Error(e);
        }
    }

    /**
     * Translate a formula into smt.
     *
     * @param formula
     *            the non-<code>null</code> formula (term of type
     *            {@link Sort#BOOL}) to be translated
     * @return an s-expression capturing the SMT translation of type Bool.
     * @throws SMTException
     */
    public SExpr trans(@NonNull Term formula) throws SMTException {
        return formula.accept(this, BOOL);
    }

    /*
     * Quantifiers are translated as follows:
     *
     * {@code Q x:T ; phi}
     *
     * becomes
     *
     * {@code (Q ((var$x universe)) (=> (TY x) (SMT phi)))}
     *
     * TY is computed by {@link #typingPredicate(SExpr, Sort)}.
     */
    @Override
    public SExpr visit(QuantTerm term, Type arg) throws SMTException {

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
        String varname = "var$" + boundVar.getName();

        SExpr qvar = new SExpr(varname, "universe");
        SExpr qqvar = new SExpr(qvar);
        SExpr sortRest = typingPredicate(new SExpr(varname), boundVar.getSort());
        SExpr formula = term.getTerm(0).accept(this, BOOL);
        SExpr impl = new SExpr("=>", sortRest, formula);

        return adjust(new SExpr(quantifier, BOOL, qqvar, impl), arg);
    }

    /*
     * An sexpr has a builtin type SExpr#getType, but another might be required.
     * This method allows one to wrap expr into a conversion function that
     * returns a sexpr of type targetType.
     *
     * Some times cannot be translated from one type to another. An SMTException
     * is thrown in such cases.
     */
    private SExpr adjust(SExpr expr, Type targetType) throws SMTException {
        Type type = expr.getType();
        if(type == targetType) {
            return expr;
        }

        switch(targetType) {
        case UNIVERSE:
            switch(type) {
            case BOOL:
                return new SExpr("b2u", UNIVERSE, expr);
            case INT:
                return new SExpr("i2u", UNIVERSE, expr);
            case UNIVERSE:
                return expr;
            default:
                throw new SMTException("Cannot adjust " + expr +
                        "from " + type +
                        " to " + targetType);
            }

        case NONE:
            return expr; // well ... do not care

        case BOOL:
            if(type != UNIVERSE) {
                throw new SMTException("Cannot adjust " + expr +
                        " from " + type +
                        " to " + targetType);
            }
            return new SExpr("u2b", BOOL, expr);

        case INT:
            if(type != UNIVERSE) {
                throw new SMTException("Cannot adjust " + expr +
                        " from " + type +
                        " to " + targetType);
            }
            return new SExpr("u2i", INT, expr);

        case HEAP:
            if(type != UNIVERSE) {
                throw new SMTException("Cannot adjust " + expr +
                        " from " + type +
                        " to " + targetType);
            }
            return new SExpr("u2h", HEAP, expr);

        default:
            throw new Error("unreachable");
        }
    }


    /*
     * translate a sort into the corresponding smt expression
     * of type "type".
     *
     * int becomes ty$int
     * C (class) becomes class$C
     * array<int> becomes (ty$array ty$int)
     */
    private static SExpr sortTerm(Sort sort) {
        List<Sort> args = sort.getArguments();
        if(args.isEmpty()) {
            return new SExpr("ty$" + sort.getName());
        } else {
            List<SExpr> children = Util.map(args, SMTTrans::sortTerm);
            return new SExpr("ty$" + sort.getName(), children);
        }
    }

    @Override
    public SExpr visit(SchemaVarTerm term, Type arg) {
        throw new UnsupportedOperationException("Schema variables are not supported for SMT solving");
    }

    /*
     * Variable names are prefixed with "var$".
     */
    @Override
    public SExpr visit(VariableTerm term, Type arg) throws SMTException {
        return adjust(new SExpr("var$" + term.getName(), UNIVERSE), arg);
    }

    /*
     * Let expressions are translated into let expression in SMT.
     *
     * The target type is deferred to the inner term, all variable
     * assignments are universe.
     */
    @Override
    public SExpr visit(LetTerm letTerm, Type arg) throws SMTException {
        SExpr inner = letTerm.getTerm(0).accept(this, arg);
        List<SExpr> substitutions = new ArrayList<SExpr>();
        for (Pair<VariableTerm, Term> pair : letTerm.getSubstitutions()) {
            substitutions.add(new SExpr("var$" + pair.fst.getName(), pair.snd.accept(this, UNIVERSE)));
        }
        return new SExpr("let", UNIVERSE, new SExpr(substitutions), inner);
    }

    @Override
    public SExpr visit(ApplTerm term, Type arg) throws SMTException {

        FunctionSymbol f = term.getFunctionSymbol();
        String name = f.getName();
        OperatorEntry entry = OP_MAP.lookup(name);
        if(entry == null && f instanceof InstantiatedFunctionSymbol) {
            InstantiatedFunctionSymbol ifs = (InstantiatedFunctionSymbol) f;
            String basename = ifs.getFamily().getBaseName();
            entry = OP_MAP.lookup(basename);
        }

        if(entry != null) {
            SMTExporter exporter = entry.getExporter();
            return adjust(exporter.translate(entry, this, term), arg);
        }

        if(name.matches("[0-9]+")) {
            return adjust(new SExpr(f.getName(), INT), arg);
        }

        List<SExpr> children = new ArrayList<>();
        for (Term subterm : term.getSubterms()) {
            children.add(subterm.accept(this, UNIVERSE));
        }

        if (!name.contains("$")) {
            name = "fct$" + name;
        }

        return adjust(new SExpr(name, UNIVERSE, children), arg);
    }

    public static OperatorEntry getOperationEntry(String name) {
        return OP_MAP.lookup(name);
    }

    public static SExpr typingPredicate(SExpr expr, Sort sort) {
        if(sort.equals(Sort.OBJECT)) {
            return new SExpr("ty$ref", expr);
        }

        SExpr sexpSort = sortTerm(sort);
        // TODO FIXME. Type parameters omitted
        SExpr result = new SExpr("=", new SExpr("ty", expr), sexpSort);

        if(sort.isClassSort()) {
            SExpr nullTy = new SExpr("=", new SExpr("ty", expr), new SExpr("ty$null"));
            result = new SExpr("or", result, nullTy);
        }

        return result;
    }

}
