/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 *
 */

package edu.kit.iti.algover.term.builder;

import edu.kit.iti.algover.data.BuiltinSymbols;
import edu.kit.iti.algover.data.MapSymbolTable;
import edu.kit.iti.algover.parser.DafnyFileParser;
import edu.kit.iti.algover.parser.DafnyParser;
import edu.kit.iti.algover.parser.DafnyTree;
import edu.kit.iti.algover.project.Project;
import edu.kit.iti.algover.term.FunctionSymbol;
import edu.kit.iti.algover.term.Sort;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.term.parser.TermParser;
import edu.kit.iti.algover.util.ImmutableList;
import edu.kit.iti.algover.util.Pair;
import edu.kit.iti.algover.util.TestUtil;
import org.junit.Before;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.ExpectedException;

import java.util.ArrayList;
import java.util.Collection;

import static org.junit.Assert.*;

public class TreeAssignmentTranslatorTest {

    @Rule
    public ExpectedException thrown = ExpectedException.none();

    private FunctionSymbol heap = BuiltinSymbols.HEAP;

    private MapSymbolTable symbTable;

    @Before
    public void setupTable() {
        Collection<FunctionSymbol> map = new ArrayList<>();
        symbTable = new MapSymbolTable(new BuiltinSymbols(), map);
    }


    // revealed a bug
    @Test
    public void letCascade() throws Exception {

        DafnyTree tree = DafnyFileParser.parse(getClass().getResourceAsStream("proj1/treeTransTest.dfy"));
        Project p = TestUtil.mockProject(tree);

        DafnyTree method = p.getMethod("m").getRepresentation();
        DafnyTree block = method.getFirstChildWithType(DafnyParser.BLOCK);

        DafnyTree post = method.getFirstChildWithType(DafnyParser.ENSURES).getLastChild();

        ImmutableList<DafnyTree> assignments =
                ImmutableList.<DafnyTree>from(block.getChildren().subList(1, block.getChildCount()));

        FunctionSymbol x = new FunctionSymbol("x", Sort.INT);
        FunctionSymbol i1 = new FunctionSymbol("i1", Sort.INT);
        FunctionSymbol i2 = new FunctionSymbol("i2", Sort.INT);
        symbTable.addFunctionSymbol(x);
        symbTable.addFunctionSymbol(i1);
        symbTable.addFunctionSymbol(i2);

        TreeAssignmentTranslator tat = new TreeAssignmentTranslator(symbTable);

        ImmutableList<Pair<FunctionSymbol, Term>> result = tat.translateAssignments(assignments);

        ImmutableList<Pair<FunctionSymbol, Term>> expected = ImmutableList.from(
                new Pair<>(x, TermParser.parse(symbTable, "5")),
                new Pair<>(x, TermParser.parse(symbTable, "i1+x")),
                new Pair<>(i2, TermParser.parse(symbTable, "i1*2")));

        assertEquals(expected, result);
    }

    @Test
    public void letCascadeHeap() throws Exception {

        symbTable.addFunctionSymbol(new FunctionSymbol("this", Sort.getClassSort("C")));
        symbTable.addFunctionSymbol(new FunctionSymbol("d", Sort.getClassSort("D")));
        symbTable.addFunctionSymbol(new FunctionSymbol("C$$field", Sort.get("field", Sort.getClassSort("C"), Sort.INT)));
        symbTable.addFunctionSymbol(new FunctionSymbol("D$$field", Sort.get("field", Sort.getClassSort("D"), Sort.getClassSort("D"))));



        DafnyTree tree = DafnyFileParser.parse(getClass().getResourceAsStream("proj1/treeTransTest.dfy"));
        Project p = TestUtil.mockProject(tree);

        DafnyTree method = p.getClass("C").getMethod("n").getRepresentation();
        DafnyTree block = method.getFirstChildWithType(DafnyParser.BLOCK);

        DafnyTree post = method.getFirstChildWithType(DafnyParser.ENSURES).getLastChild();

        ImmutableList<DafnyTree> assignments =
                ImmutableList.<DafnyTree>from(block.getChildren());

        assertNotNull(symbTable);

        TreeAssignmentTranslator tat = new TreeAssignmentTranslator(symbTable);

        ImmutableList<Pair<FunctionSymbol, Term>> result = tat.translateAssignments(assignments);

        // Code is :
        //   field := field + 1;
        //   d.field := null;
        ImmutableList<Pair<FunctionSymbol, Term>> expected = ImmutableList.from(
                new Pair<>(heap, TermParser.parse(symbTable, "$store<C, int>($heap, this, C$$field, $select<C,int>($heap, this, C$$field) + 1)")),
                new Pair<>(heap, TermParser.parse(symbTable, "$store<D, D>($heap, d, D$$field, null)")));

        assertEquals(expected, result);
    }

    @Test
    public void letCascadeSeq() throws Exception {
        symbTable.addFunctionSymbol(new FunctionSymbol("this", Sort.getClassSort("Seq")));
        symbTable.addFunctionSymbol(new FunctionSymbol("Seq$$fsq",
                Sort.get("field", Sort.getClassSort("Seq"), Sort.get("seq", Sort.INT))));
        FunctionSymbol sq = new FunctionSymbol("sq", Sort.get("seq", Sort.INT));
        symbTable.addFunctionSymbol(sq);

        DafnyTree tree = DafnyFileParser.parse(getClass().getResourceAsStream("proj1/treeTransTest.dfy"));
        Project p = TestUtil.mockProject(tree);

        DafnyTree method = p.getClass("Seq").getMethod("s").getRepresentation();
        DafnyTree block = method.getFirstChildWithType(DafnyParser.BLOCK);

        ImmutableList<DafnyTree> assignments =
                ImmutableList.<DafnyTree>from(block.getChildren()).
                        filter(x -> x.getType() == DafnyParser.ASSIGN);

        DafnyTree post = method.getFirstChildWithType(DafnyParser.ENSURES).getLastChild();

        TreeAssignmentTranslator tat = new TreeAssignmentTranslator(symbTable);

        ImmutableList<Pair<FunctionSymbol, Term>> result = tat.translateAssignments(assignments);

        ImmutableList<Pair<FunctionSymbol, Term>> expected = ImmutableList.from(
                new Pair<>(sq, TermParser.parse(symbTable, "$seq_upd<int>(sq, 0, 2)")),
                new Pair<>(heap, TermParser.parse(symbTable, "$store<Seq, seq<int>>($heap, this, Seq$$fsq, $seq_upd<int>($select<Seq, seq<int>>($heap, this, Seq$$fsq), 1, 3))")),
                new Pair<>(heap, TermParser.parse(symbTable, "$store<Seq, seq<int>>($heap, this, Seq$$fsq, $seq_upd<int>($select<Seq, seq<int>>($heap, this, Seq$$fsq), 2, 4))")));


        assertEquals(expected, result);
    }


}