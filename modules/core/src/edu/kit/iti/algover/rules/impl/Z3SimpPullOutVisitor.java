/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 *
 */

package edu.kit.iti.algover.rules.impl;

import de.uka.ilkd.pp.NoExceptions;
import edu.kit.iti.algover.data.BuiltinSymbols;
import edu.kit.iti.algover.rules.DefaultFocusProofRule;
import edu.kit.iti.algover.rules.NotApplicableException;
import edu.kit.iti.algover.rules.RuleException;
import edu.kit.iti.algover.smt.SMTQuickNDirty;
import edu.kit.iti.algover.term.ApplTerm;
import edu.kit.iti.algover.term.DefaultTermVisitor;
import edu.kit.iti.algover.term.FunctionSymbol;
import edu.kit.iti.algover.term.SchemaTerm;
import edu.kit.iti.algover.term.Sort;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.term.TermVisitor;
import edu.kit.iti.algover.term.builder.ReplacementVisitor;
import edu.kit.iti.algover.term.builder.TermBuildException;
import edu.kit.iti.algover.util.Util;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

class Z3SimpPullOutVisitor extends DefaultTermVisitor<StringBuilder, String, RuleException> {

    private static final String PLACEHOLDER = "placeholder_";

    private static Map<FunctionSymbol, String> SUPPORTED_SYMBOLS =
            supportedSymbol();

    private List<Term> replacedTerms = new ArrayList<>();

    private static Map<FunctionSymbol, String> supportedSymbol() {
        Map<FunctionSymbol, String> result = new HashMap<>();
        result.put(BuiltinSymbols.PLUS, "+");
        result.put(BuiltinSymbols.MINUS, "-");
        // TODO < > <= / * == !=, unary minus
        return result;
    }

    @Override
    public String visit(ApplTerm term, StringBuilder decls) throws RuleException {
        if (!term.getSort().equals(Sort.INT)) {
            throw new NotApplicableException("Only integer terms can be simplified");
        }

        FunctionSymbol function = term.getFunctionSymbol();
        String smtSymbol = SUPPORTED_SYMBOLS.get(function);
        if (smtSymbol == null) {
            // replace by new placeholder
            String placeholder = PLACEHOLDER + replacedTerms.size();
            decls.append(String.format("(define-const %s Int %s)%n", placeholder, term.accept(new SMTQuickNDirty(), null)));
            replacedTerms.add(term);
            return placeholder;
        } else {
            return String.format("(%s %s)", smtSymbol,
                    Util.join(Util.map(term.getSubterms(), t -> t.accept(this, decls)), " "));
        }
    }

    @Override
    protected String defaultVisit(Term term, StringBuilder arg) throws RuleException {
        throw new NotApplicableException("Only simple integer terms can be simplified");
    }

    @Override
    public String visitSchemaTerm(SchemaTerm schemaTerm, StringBuilder arg) throws RuleException {
        throw new RuleException("There should not be a schematic term here");
    }

    public List<Term> getReplacedTerms() {
        return replacedTerms;
    }
}
