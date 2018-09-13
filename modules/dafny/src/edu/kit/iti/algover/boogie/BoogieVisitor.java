/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 *
 */

package edu.kit.iti.algover.boogie;

import de.uka.ilkd.pp.NoExceptions;
import edu.kit.iti.algover.term.ApplTerm;
import edu.kit.iti.algover.term.DefaultTermVisitor;
import edu.kit.iti.algover.term.FunctionSymbol;
import edu.kit.iti.algover.term.FunctionSymbolFamily.InstantiatedFunctionSymbol;
import edu.kit.iti.algover.term.LetTerm;
import edu.kit.iti.algover.term.QuantTerm;
import edu.kit.iti.algover.term.QuantTerm.Quantifier;
import edu.kit.iti.algover.term.Sort;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.term.VariableTerm;
import edu.kit.iti.algover.util.Util;

import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;

import static edu.kit.iti.algover.data.BuiltinSymbols.*;

/**
 * This visitor is used to translate AlgoVer {@link Term} objects into Strings
 * representing corresponding (semantically equivalent in their respective
 * logics) Strings in Boogie.
 *
 * The translation is restricted to a part of the logic.
 *
 * A table is kept for the built in function symbols which are translated using
 * the functions stored in that map. The interface {@link Boogiefier} is used for
 * such translation functions.
 *
 * (I have been using Scala lately. One can tell.)
 *
 * @author mulbrich
 */
public class BoogieVisitor extends DefaultTermVisitor<Void, String, NoExceptions> {

    /**
     * The functional interface for the routines which translate individual
     * function symbols.
     */
    @FunctionalInterface
    private interface Boogiefier {
        /**
         * Translate a term into a Boogie string
         * @param term the term to translate, not null
         * @param visitor the visitor to use for subterms, not null
         * @return a non-null String
         */
        String translate(ApplTerm term, BoogieVisitor visitor);
    }


    private static final Map<String, Boogiefier> FUNCTIONS = prepareMap();
    private static Map<String, Boogiefier> prepareMap() {
        Map<String, Boogiefier> result = new HashMap<>();
        // --- Integers
        result.put(PLUS.getName(), binary("+"));
        result.put(MINUS.getName(), binary("-"));
        result.put(TIMES.getName(), binary("*"));
        result.put(GE.getName(), binary(">="));
        result.put(GT.getName(), binary(">"));
        result.put(LE.getName(), binary("<="));
        result.put(LT.getName(), binary("<"));
        // --- FOL
        result.put(EQ.getBaseName(), equal());
        result.put(AND.getName(), binary("&&"));
        result.put(IMP.getName(), binary("==>"));
        result.put(OR.getName(), binary("||"));
        result.put(NOT.getName(), (t,v) -> "!("+t.getTerm(0).accept(v,null)+")");
        // --- Sets
        result.put(SUBSET.getBaseName(), function("Set#Subset"));
        result.put(UNION.getBaseName(), function("Set#Union"));
        result.put(INTERSECT.getBaseName(), function("Set#Intersection"));
        result.put(SET_MINUS.getBaseName(), function("Set#Difference"));
        result.put(UNION.getBaseName(), function("Set#Union"));
        result.put(SET_ADD.getBaseName(), function("Set#UnionOne", true));
        result.put(SET_IN.getBaseName(), setIn());
        result.put(EMPTY_SET.getName(), function("Set#Empty"));
        // --- Sequents
        result.put(SEQ_LEN.getBaseName(), function("Seq#Length"));
        result.put(SEQ_GET.getBaseName(), function("Seq#Index"));
        result.put(SEQ_EMPTY.getName(), function("Seq#Empty"));
        result.put(SEQ_UPDATE.getBaseName(), function("Seq#Update"));
        result.put(SEQ_SUB.getBaseName(), seqSub());
        result.put(SEQ_CONS.getBaseName(), function("Seq#Build", true));
        result.put(SEQ_CONCAT.getBaseName(), function("Seq#Append"));
        return result;
    }

    private static Boogiefier seqSub() {
        return (t,v) -> {
            String seq = t.getTerm(0).accept(v, null);
            String from = t.getTerm(1).accept(v, null);
            String to = t.getTerm(2).accept(v, null);
            return "Seq#Drop(Seq#Take(" + seq + ", " + to + "), " + from + ")";
        };
    }


    /*
     * Returns a Boogiefier that translates
     *    f(x, ..., y)
     * into
     *    fctName(v(x), ..., v(y)
     * where v(...) is the applcation of the provided visitor.
     */
    private static final Boogiefier function(String fctName) {
        return function(fctName, false);
    }

    /*
     * Returns a Boogiefier that translates
     *    f(x, ..., y)
     * into
     *    fctName(v(x), ..., v(y)
     * if reverse == false and
     *    fctName(v(y), ..., v(y)
     * otherwie
     * where v(...) is the applcation of the provided visitor.
     */
    private static Boogiefier function(String fctName, boolean reverse) {

        return (t,v) -> {
            StringBuilder sb = new StringBuilder(fctName);
            List<String> visited = Util.map(t.getSubterms(), x -> x.accept(v, null));
            if (reverse) {
                Collections.reverse(visited);
            }
            sb.append("(").append(Util.commatize(visited)).append(")");
            return sb.toString();
        };
    }

    /*
     * Equal is special. x==y becomes:
     *    Set#Equal(v(x), v(y)) for sets
     *    Set#Equal(v(x), v(y)) for sequenes
     *    (v(x)==v(y))  otherwise
     */
    private static final Boogiefier equal() {
        return (t, v) -> {
            Boogiefier f;
            switch (t.getTerm(0).getSort().getName()) {
            case "set":
                f = function("Set#Equal");
                break;
            case "seq":
                f = function("Seq#Equal");
                break;
            default:
                f = binary("==");
                break;
            }
            return f.translate(t, v);
        };
    }

    /*
     * For set membership, Boogie uses map syntax:
     *    set_in(e, s)    becomes    ( v(s) [ v(e) ])
     */
    private static Boogiefier setIn() {
        return (t,v) -> {
            String set = t.getTerm(1).accept(v, null);
            String elem = t.getTerm(0).accept(v, null);
            return "(" + set + "[" + elem + "])";
        };
    }


    /*
     *  Binary infix symbol. f(x,y) becomes
     *     "(" v(x) "op" v(y) ")"
     */
    private static Boogiefier binary(String op) {
        return (t,v) -> {
            assert t.countTerms()==2;
            String left = t.getTerm(0).accept(v, null);
            String right = t.getTerm(1).accept(v, null);
            return "(" + left + " " + op + " " + right + ")";
        };
    }

    // ------------------ End of static part


    /**
     * This collection keeps all required declarations which were collected
     * so far.
     */
    private Set<String> declarations = new TreeSet<>();

    /*
     * Check for an entry in the map, otherwise declare the constant.
     */
    @Override
    public String visit(ApplTerm term, Void arg) {
        FunctionSymbol fs = term.getFunctionSymbol();
        String name = fs.getName();
        if (fs instanceof InstantiatedFunctionSymbol) {
            InstantiatedFunctionSymbol instantiatedFunctionSymbol = (InstantiatedFunctionSymbol) fs;
            name = instantiatedFunctionSymbol.getFamily().getBaseName();
        }

        if (name.matches("[0-9]+")) {
            // Numbers are function symbols, too.
            return name;
        }

        Boogiefier handler = FUNCTIONS.get(name);
        if (handler != null) {
            return handler.translate(term, this);
        }

        if(fs.getArity() == 0) {
            declarations.add(String.format("var _%s : %s;", name, visitSort(fs.getResultSort())));
            return "_" + name;
        }

        assert !(fs instanceof InstantiatedFunctionSymbol) :
                "This should have been in the table: " + name;

        // here we hope that no clash will occur ...
        declarations.add(String.format("function fct_%s(%s) : %s;",
                name,
                Util.commatize(Util.map(fs.getArgumentSorts(), BoogieVisitor::visitSort)),
                visitSort(fs.getResultSort())));

        return function("fct_" + name).translate(term, this);
    }

    @Override
    protected String defaultVisit(Term term, Void arg) throws NoExceptions {
        throw new IllegalStateException("This should not be reached");
    }

    @Override
    public String visit(LetTerm term, Void arg) throws NoExceptions {
        throw new IllegalStateException("This should not be reached. " +
                "Let-expressions should have been resolved");
    }

    /*
     * Variables are prefixed with var_
     */
    @Override
    public String visit(VariableTerm term, Void arg) throws NoExceptions {
        return "var_" + term.getName();
    }

    /*
     * Quantifiers are straight forward.
     */
    @Override
    public String visit(QuantTerm term, Void arg) throws NoExceptions {
        String quantifier = term.getQuantifier() == Quantifier.FORALL ?
                "forall" : "exists";

        return "(" + quantifier + " var_" + term.getBoundVar().getName() + " : " +
        visitSort(term.getBoundVar().getSort()) + " :: " +
        term.getTerm(0).accept(this, null) + ")";
    }

    private static String visitSort(Sort sort) {
        switch(sort.getName()) {
        case "seq" :
            return "Seq " + visitSort(sort.getArgument(0));
        case "set" :
            return "Set " + visitSort(sort.getArgument(0));
        case "bool":
        case "int":
            return sort.getName();
        }
        return sort.toString();
    }

    public Set<String> getDeclarations() {
        return declarations;
    }
}
