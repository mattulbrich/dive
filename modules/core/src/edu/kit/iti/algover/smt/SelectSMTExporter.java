/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.smt;

import java.util.List;

import edu.kit.iti.algover.data.BuiltinSymbols;
import edu.kit.iti.algover.smt.SMTOperatorMap.OperatorEntry;
import edu.kit.iti.algover.smt.SMTOperatorMap.SMTExporter;
import edu.kit.iti.algover.term.ApplTerm;
import edu.kit.iti.algover.term.FunctionSymbol;
import edu.kit.iti.algover.term.FunctionSymbolFamily;
import edu.kit.iti.algover.term.FunctionSymbolFamily.InstantiatedFunctionSymbol;
import edu.kit.iti.algover.term.Sort;
import edu.kit.iti.algover.term.Term;

public class SelectSMTExporter implements SMTExporter {

    @Override
    public SExpr translate(OperatorEntry entry, SMTTrans trans, ApplTerm term) throws SMTException {

        FunctionSymbol fs = term.getFunctionSymbol();
        if(!(fs instanceof InstantiatedFunctionSymbol)) {
            throw new SMTException("This term cannot be translated using this exporter!");
        }
        FunctionSymbolFamily family = ((InstantiatedFunctionSymbol)fs).getFamily();

        if(family == BuiltinSymbols.SELECT) {
            throw new Error("t b d");
        } else if(family == BuiltinSymbols.ARRAY_SELECT) {
            return translateArraySelect(trans, term);
        } else if(family == BuiltinSymbols.ARRAY2_SELECT) {
            throw new Error("t b d");
        } else {
            throw new SMTException("This term cannot be translated using this exporter!");
        }

    }

    private SExpr translateArraySelect(SMTTrans trans, ApplTerm term) throws SMTException {
        List<Term> subterms = term.getSubterms();

        Sort type = term.getSort();

        Term heap = subterms.get(0);
        Term obj = subterms.get(1);
        Term index = subterms.get(2);

        SExpr heapSMT = heap.accept(trans, SExpr.Type.HEAP);
        SExpr objSMT = obj.accept(trans, SExpr.Type.UNIVERSE);
        SExpr indexSMT = new SExpr("arrIdx", index.accept(trans, SExpr.Type.INT));

        SExpr select = new SExpr("select", SExpr.Type.UNIVERSE, heapSMT, objSMT, indexSMT);
        return SMTTrans.coerce(select, type);
    }

}
