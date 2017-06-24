/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.term.builder;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

import java.io.File;
import java.util.ArrayList;
import java.util.Collection;

import org.antlr.runtime.ANTLRStringStream;
import org.antlr.runtime.CommonTokenStream;
import org.antlr.runtime.RecognitionException;
import org.junit.Before;
import org.junit.Ignore;
import org.junit.Test;
import org.junit.runner.RunWith;

import edu.kit.iti.algover.data.BuiltinSymbols;
import edu.kit.iti.algover.data.MapSymbolTable;
import edu.kit.iti.algover.parser.DafnyFileParser;
import edu.kit.iti.algover.parser.DafnyLexer;
import edu.kit.iti.algover.parser.DafnyParser;
import edu.kit.iti.algover.parser.DafnyParser.expression_only_return;
import edu.kit.iti.algover.parser.DafnyTree;
import edu.kit.iti.algover.project.Project;
import edu.kit.iti.algover.term.ApplTerm;
import edu.kit.iti.algover.term.FunctionSymbol;
import edu.kit.iti.algover.term.LetTerm;
import edu.kit.iti.algover.term.Sort;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.term.VariableTerm;
import edu.kit.iti.algover.term.parser.TermParser;
import edu.kit.iti.algover.util.ImmutableList;
import edu.kit.iti.algover.util.TestUtil;
import junitparams.JUnitParamsRunner;
import junitparams.Parameters;


@RunWith(JUnitParamsRunner.class)
public class TreeTermTranslatorTest {

    private static final File FILE = new File("modules/core/test-res/edu/kit/iti/algover/term/builder/proj1");

    public String[][] parametersForTestTermTranslation() {
        return new String[][] {
            { "i1 + i2*i3", "$plus(i1, $times(i2, i3))" },
            // revealed bug:
            { "i1 == i2*i3", "$eq<int>(i1, $times(i2, i3))" },
            { "a.Length", "$len0(a)" },
            //                { "a2.Length0", "$len0(a)" },
            //                { "a2.Length1", "$len1(a)" },
            // no 2-dim arrays for now

            // for coverage:
            { "i1 > i2", "$gt(i1, i2)" },
            { "i1 >= i2", "$ge(i1, i2)" },
            { "i1 < i2", "$lt(i1, i2)" },
            { "i1 <= i2", "$le(i1, i2)" },
            { "i1 == i2", "$eq<int>(i1, i2)" },
            { "b1 == b2", "$eq<bool>(b1, b2)" },
            { "i1 != i2", "$not($eq<int>(i1, i2))" },
            { "i1 - 1 - 2", "$minus($minus(i1, 1), 2)" },

            { "false && true", "$and(false, true)" },
            { "b1 || b2 ==> b3", "$imp($or(b1, b2), b3)" },
            { "forall x:int :: exists y:int :: x > y",
            "(forall x:int :: (exists y:int :: $gt(x, y)))" },
            { "let x := 3 :: x > i1", "(let x := 3 :: $gt(x, i1))" },
            { "$plus(1, 2)", "$plus(1, 2)" },

            { "c == null", "$eq<object>(c, null)" },
            { "c == c2", "$eq<object>(c, c2)" },
            { "let c := null :: null == c",
                "(let c := null :: $eq<object>(null, c))" },

            // From TermParserTest
            { "i1 + i2", "$plus(i1, i2)" },
            { "forall i: int :: 0 < i ==> i > 0",
              "(forall i:int :: $imp($lt(0, i), $gt(i, 0)))" },
            { "let var x := i1+5 ; x*2",
              "(let x := $plus(i1, 5) :: $times(x, 2))" },
            { "let var i1, i2 := i2, i1 :: i1 + i2",
              "(let i1, i2 := i2, i1 :: $plus(i1, i2))" },
            { "if i1 > 5 then i2 else i1",
              "$ite<int>($gt(i1, 5), i2, i1)" },
        };
    }

    public String[][] parametersForFailingParser() {
        return new String[][] {
            { "unknownFunction(1)", "Unknown symbol unknownFunction" },
            { "unknownIdentifier", "Unknown identifier unknownIdentifier" },
            { "b1 == i1", "Unexpected argument sort for argument 2" },
            { "let x,y:=1 :: y", "Mismatched assignments in let expression:" },
            { "let x:=1 :: unknown", "" },  // no more bound vars after this
            { "forall x:int :: unknown", "" },  // no more bound vars after this
            { "f(b1)", "Unexpected argument sort" },
            { "if true then b1 else i1", "Unexpected argument sort" },
        };
    }

    private static DafnyTree parse(String s) throws RecognitionException {
        // create the lexer attached to stream
        ANTLRStringStream input = new ANTLRStringStream(s);

        DafnyLexer lexer = new DafnyLexer(input);
        // create the buffer of tokens between the lexer and parser
        CommonTokenStream tokens = new CommonTokenStream(lexer);
        // create the parser attached to the token buffer
        DafnyParser parser = new DafnyParser(tokens);
        parser.setTreeAdaptor(new DafnyTree.Adaptor());
        parser.setLogicMode(true);
        // launch the parser starting at rule r, get return object
        expression_only_return result;
        try {
            result = parser.expression_only();
            DafnyTree t = result.getTree();
            if(input.LA(1) != DafnyParser.EOF) {
                throw new RecognitionException(input);
            }
            return t;
        } catch (RecognitionException e) {
            System.err.println(parser.getErrorMessage(e, parser.getTokenNames()));
            throw e;
        }
        // pull out the tree and cast it
    }

    private MapSymbolTable symbTable;

    @Before
    public void setupTable() {
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
        symbTable = new MapSymbolTable(new BuiltinSymbols(), map);
    }

    @Test @Parameters
    public void testTermTranslation(String input, String expected) throws Exception {
        assertNotNull(symbTable);

        TreeTermTranslator ttt = new TreeTermTranslator(symbTable);

        DafnyTree t = parse(input);
        Term term = ttt.build(t);

        assertEquals(expected, term.toString());
        assertEquals(0, ttt.countBoundVars());
    }

    @Test @Parameters
    public void failingParser(String input, String errMsg) throws Exception {
        assertNotNull(symbTable);

        TreeTermTranslator ttt = new TreeTermTranslator(symbTable);

        DafnyTree t = parse(input);
        try {
            ttt.build(t);
            fail("Should not reach this here");
        } catch (TermBuildException e) {
            if(!e.getMessage().contains(errMsg)) {
                e.printStackTrace();
            }
            assertTrue(e.getMessage().contains(errMsg));
            assertEquals(0, ttt.countBoundVars());
        }

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

        assertNotNull(symbTable);

        TreeTermTranslator ttt = new TreeTermTranslator(symbTable);

        Term result = ttt.build(assignments, post);

        Term expected = TermParser.parse(symbTable,
                "let x:=5 :: let x:=i1+x :: let i2 := i1*2 :: i2 > 0");

        assertEquals(expected, result);
    }

    @Test @Ignore // expected result cannot yet be parsed
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

        TreeTermTranslator ttt = new TreeTermTranslator(symbTable);

        Term result = ttt.build(assignments, post);

        Term expected = TermParser.parse(symbTable,
                "let heap := $store<C,int>($heap, this, C$$field, "
                + "$plus($select<C, int>($heap, this, C$$field), 1)) :: "
                + "let heap := $store<D, D>(heap, d, D$$field, null[D]) :: "
                + "$select<C, int>(heap, this, C$$field) > 1");

        assertEquals(expected, result);
    }

    // from a bug
    @Test
    public void testLetProblem() throws Exception {

        TreeTermTranslator ttt = new TreeTermTranslator(symbTable);
        DafnyTree t = parse("let var i1, i2 := i2, i1 :: i1 + i2");
        Term term = ttt.build(t);

        Term sum1 = ((LetTerm)term).getSubstitutions().get(0).snd;
        Term sum2 = ((LetTerm)term).getSubstitutions().get(0).snd;

        assertTrue(sum1 instanceof ApplTerm);
        assertTrue(sum2 instanceof ApplTerm);

        sum1 = term.getTerm(0).getTerm(0);
        sum2 = term.getTerm(0).getTerm(0);
        assertTrue(sum1 instanceof VariableTerm);
        assertTrue(sum2 instanceof VariableTerm);
    }

}
