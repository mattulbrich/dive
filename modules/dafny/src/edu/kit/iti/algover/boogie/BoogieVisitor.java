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

import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.function.BiFunction;
import java.util.function.Function;

public class BoogieVisitor extends DefaultTermVisitor<Void, String, NoExceptions> {

    private static final Map<String, BiFunction<ApplTerm, BoogieVisitor, String>> FUNCTIONS = prepareMap();

    private static Map<String,BiFunction<ApplTerm,BoogieVisitor,String>> prepareMap() {
        Map<String, BiFunction<ApplTerm, BoogieVisitor, String>> result = new HashMap<>();
        result.put("$plus", binary("+"));
        result.put("$minus", binary("-"));
        result.put("$times", binary("*"));
        result.put("$ge", binary(">="));
        result.put("$gt", binary(">"));
        result.put("$le", binary("<="));
        result.put("$lt", binary("<"));
        result.put("$eq", binary("=="));
        result.put("$and", binary("&&"));
        result.put("$not", (t,v) -> "!("+t.getTerm(0).accept(v,null)+")");
        return result;
    }

    private static final BiFunction<ApplTerm,BoogieVisitor,String> AS_FCT =
            (t,v) -> {
                if(t.countTerms() == 0) {
                    return t.getFunctionSymbol().getName();
                }
                List<String> visited = Util.map(t.getSubterms(), x -> x.accept(v, null));
                return t.getFunctionSymbol().getName() + "(" + Util.commatize(visited) + ")";
            };

    private static BiFunction<ApplTerm,BoogieVisitor,String> binary(String op) {
        return (t,v) -> {
            assert t.countTerms()==2;
            String left = t.getTerm(0).accept(v, null);
            String right = t.getTerm(1).accept(v, null);
            return "(" + left + " " + op + " " + right + ")";
        };
    }

    @Override
    public String visit(ApplTerm term, Void arg) throws NoExceptions {
        FunctionSymbol fs = term.getFunctionSymbol();
        String name = fs.getName();
        if (fs instanceof InstantiatedFunctionSymbol) {
            InstantiatedFunctionSymbol instantiatedFunctionSymbol = (InstantiatedFunctionSymbol) fs;
            name = instantiatedFunctionSymbol.getFamily().getBaseName();
        }

        BiFunction<ApplTerm, BoogieVisitor, String> handler = FUNCTIONS.getOrDefault(name, AS_FCT);
        return handler.apply(term, this);

    }

    @Override
    protected String defaultVisit(Term term, Void arg) throws NoExceptions {
        return null;
    }

    @Override
    public String visit(VariableTerm term, Void arg) throws NoExceptions {
        return "var_" + term.getName();
    }

    @Override
    public String visit(LetTerm term, Void arg) throws NoExceptions {
        throw new RuntimeException();
    }

    @Override
    public String visit(QuantTerm term, Void arg) throws NoExceptions {
        String quantifier = term.getQuantifier() == Quantifier.FORALL ?
                "forall" : "exists";

        return "(" + quantifier + " var_" + term.getBoundVar().getName() + " : " +
        visitSort(term.getBoundVar().getSort()) + " :: " +
        term.getTerm(0).accept(this, null) + ")";
    }

    private String visitSort(Sort sort) {
        switch(sort.getName()) {
        case "seq" :
            return "Seq<" + visitSort(sort.getArgument(0)) + ">";
        case "bool":
        case "int":
            return sort.getName();
        }
        return sort.toString();
    }
}
