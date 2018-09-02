/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.term.builder;

import static org.junit.Assert.assertEquals;

import java.io.InputStream;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import edu.kit.iti.algover.parser.DafnyParser;
import org.junit.Test;

import edu.kit.iti.algover.ProgramDatabase;
import edu.kit.iti.algover.dafnystructures.DafnyMethod;
import edu.kit.iti.algover.data.BuiltinSymbols;
import edu.kit.iti.algover.data.MapSymbolTable;
import edu.kit.iti.algover.data.SymbolTable;
import edu.kit.iti.algover.parser.DafnyTree;
import edu.kit.iti.algover.parser.ParserTest;
import edu.kit.iti.algover.project.Project;
import edu.kit.iti.algover.symbex.Symbex;
import edu.kit.iti.algover.symbex.SymbexPath;
import edu.kit.iti.algover.term.FunctionSymbol;
import edu.kit.iti.algover.term.Sequent;
import edu.kit.iti.algover.term.Sort;
import edu.kit.iti.algover.util.TestUtil;
import edu.kit.iti.algover.util.TreeUtil;
import edu.kit.iti.algover.util.Util;

public abstract class SequenterTest {

    public SequenterTest() {
        super();
    }

    @Test
    public void test() throws Exception {

        InputStream is = getClass().getResourceAsStream("sequenterTest.dfy");
        DafnyTree top = ParserTest.parseFile(is, null);
        // SyntacticSugarVistor.visit(top);
        Project p = TestUtil.mockProject(top);

        Symbex symbex = new Symbex();
        DafnyMethod method = p.getMethod("m");
        List<SymbexPath> results = symbex.symbolicExecution(method.getRepresentation());
        assertEquals(2, results.size());

        SymbexPath path = results.get(1);

        PVCSequenter sequenter = makeSequenter();

        Sequent sequent = sequenter.translate(path, makeTable(method), null);

        assertEquals(expectedAntecedent(path.getPathIdentifier()),
                Util.map(sequent.getAntecedent(), x->x.getTerm()).toString());

        assertEquals(expectedSuccedent(path.getPathIdentifier()),
                Util.map(sequent.getSuccedent(), x->x.getTerm()).toString());

    }

    protected abstract PVCSequenter makeSequenter();

    protected abstract String expectedSuccedent(String pathIdentifier);

    protected abstract String expectedAntecedent(String pathIdentifier);

    protected SymbolTable makeTable(DafnyMethod method) {

        Collection<FunctionSymbol> map = new ArrayList<>();

        for (DafnyTree decl : ProgramDatabase.getAllVariableDeclarations(method.getRepresentation())) {
            String name = decl.getChild(0).toString();
            Sort sort = TreeUtil.toSort(decl.getFirstChildWithType(DafnyParser.TYPE).getChild(0));
            map.add(new FunctionSymbol(name, sort));
        }

        map.add(new FunctionSymbol("$aheap_1", Sort.HEAP));

        MapSymbolTable st = new MapSymbolTable(new BuiltinSymbols(), map);
        return st;
    }

}