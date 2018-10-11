package edu.kit.iti.algover.util;

import edu.kit.iti.algover.data.BuiltinSymbols;
import edu.kit.iti.algover.data.MapSymbolTable;
import edu.kit.iti.algover.data.SymbolTable;
import edu.kit.iti.algover.proof.ProofFormula;
import edu.kit.iti.algover.term.FunctionSymbol;
import edu.kit.iti.algover.term.Sequent;
import edu.kit.iti.algover.term.Sort;
import edu.kit.iti.algover.term.builder.TermBuildException;
import edu.kit.iti.algover.term.builder.TermBuilder;
import edu.kit.iti.algover.term.builder.TreeTermTranslator;
import edu.kit.iti.algover.term.builder.TreeTermTranslatorTest;
import org.antlr.runtime.RecognitionException;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

public class InterpreterUtils {

    public static Sequent createTestSequent(String[] antec, String[] succ, SymbolTable symbTable) throws RecognitionException, TermBuildException {
        return createTestSequentHelper(antec, succ, symbTable, false);
    }

    public static Sequent createTestSequentHelper(String[] antec, String[] succ, SymbolTable symbTable, boolean schemaEnable) throws RecognitionException, TermBuildException {
        TermBuilder tb = new TermBuilder(symbTable);
        TreeTermTranslator ttt = new TreeTermTranslator(symbTable);

        List<ProofFormula> antecTerms = new ArrayList<>();
        List<ProofFormula> succTerms = new ArrayList<>();
        for (String s : antec) {
            antecTerms.add(new ProofFormula(ttt.build(TreeTermTranslatorTest.parse(s, schemaEnable))));

        }
        for (String s : succ) {
            succTerms.add(new ProofFormula(ttt.build(TreeTermTranslatorTest.parse(s, schemaEnable))));
        }
        return new Sequent(antecTerms, succTerms);
    }

    public static SymbolTable setupTable() {
        Collection<FunctionSymbol> map = new ArrayList<>();
        map.add(new FunctionSymbol("i1", Sort.INT));
        map.add(new FunctionSymbol("i2", Sort.INT));
        map.add(new FunctionSymbol("i3", Sort.INT));
        map.add(new FunctionSymbol("b1", Sort.BOOL));
        map.add(new FunctionSymbol("b2", Sort.BOOL));
        map.add(new FunctionSymbol("b3", Sort.BOOL));
        map.add(new FunctionSymbol("a", Sort.get("array1")));
        map.add(new FunctionSymbol("a2", Sort.get("array2")));
        map.add(new FunctionSymbol("f", Sort.INT, Sort.INT));
        map.add(new FunctionSymbol("c", Sort.getClassSort("C")));
        map.add(new FunctionSymbol("c2", Sort.getClassSort("C")));
        SymbolTable symbTable = new MapSymbolTable(new BuiltinSymbols(), map);
        return symbTable;
    }
}
