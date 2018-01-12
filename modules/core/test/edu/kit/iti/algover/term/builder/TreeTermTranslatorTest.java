/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.term.builder;

import edu.kit.iti.algover.data.BuiltinSymbols;
import edu.kit.iti.algover.data.MapSymbolTable;
import edu.kit.iti.algover.parser.DafnyFileParser;
import edu.kit.iti.algover.parser.DafnyLexer;
import edu.kit.iti.algover.parser.DafnyParser;
import edu.kit.iti.algover.parser.DafnyParser.expression_only_return;
import edu.kit.iti.algover.parser.DafnyTree;
import edu.kit.iti.algover.project.Project;
import edu.kit.iti.algover.term.*;
import edu.kit.iti.algover.term.parser.TermParser;
import edu.kit.iti.algover.util.ASTUtil;
import edu.kit.iti.algover.util.ImmutableList;
import edu.kit.iti.algover.util.TestUtil;
import junitparams.JUnitParamsRunner;
import junitparams.Parameters;
import org.antlr.runtime.ANTLRStringStream;
import org.antlr.runtime.CommonTokenStream;
import org.antlr.runtime.RecognitionException;
import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;
import org.junit.runner.RunWith;

import java.util.ArrayList;
import java.util.Collection;

import static org.junit.Assert.*;


@RunWith(JUnitParamsRunner.class)
public class TreeTermTranslatorTest {

    private MapSymbolTable symbTable;

    public static DafnyTree parse(String s) throws RecognitionException {
        return parse(s, false);
    }

    public static DafnyTree parse(String s, boolean supportSchematic) throws RecognitionException {
        // create the lexer attached to stream
        ANTLRStringStream input = new ANTLRStringStream(s);

        DafnyLexer lexer = new DafnyLexer(input);
        // create the buffer of tokens between the lexer and parser
        CommonTokenStream tokens = new CommonTokenStream(lexer);
        // create the parser attached to the token buffer
        DafnyParser parser = new DafnyParser(tokens);
        parser.setTreeAdaptor(new DafnyTree.Adaptor());
        parser.setLogicMode(true);
        parser.setSchemaMode(supportSchematic);
        // launch the parser starting at rule r, get return object
        expression_only_return result;
        try {
            result = parser.expression_only();
            DafnyTree t = result.getTree();
            if (input.LA(1) != DafnyParser.EOF) {
                throw new RecognitionException(input);
            }
            return t;
        } catch (RecognitionException e) {
            System.err.println(parser.getErrorMessage(e, parser.getTokenNames()));
            throw e;
        }
        // pull out the tree and cast it
    }

    public String[][] parametersForTestTermTranslation() {
        return new String[][] {
            { "i1 + i2*i3", "$plus(i1, $times(i2, i3))" },
            // revealed bug:
            { "i1 == i2*i3", "$eq<int>(i1, $times(i2, i3))" },
                {"a.Length", "$len<int>(a)"},
                {"a2.Length0", "$len0<int>(a2)"},
                {"a2.Length1", "$len1<int>(a2)"},
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
            { "forall x,y,z:int :: x > y+z",
              "(forall x:int :: (forall y:int :: "
                 + "(forall z:int :: $gt(x, $plus(y, z)))))" },
            { "forall x:int :: exists y:int :: x > y",
              "(forall x:int :: (exists y:int :: $gt(x, y)))" },
            { "forall x,x:int :: true",
              "(forall x:int :: (forall x:int :: true))" },
            { "let x := 3 :: x > i1", "(let x := 3 :: $gt(x, i1))" },
            { "$plus(1, 2)", "$plus(1, 2)" },

            { "c == null", "$eq<object>(c, null)" },
            { "c == c2", "$eq<object>(c, c2)" },
            { "let c := null :: null == c",
                "(let c := null :: $eq<object>(null, c))" },

                // Heap accesses
                {"a[0]", "$array_select<int>($heap, a, 0)"},
                {"a2[1,2]", "$array2_select<int>($heap, a2, 1, 2)"},
                {"null", "null"},

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
                {"-1", "$neg(1)"},

                // Associativity
                {"1+2-3", "$minus($plus(1, 2), 3)"},
                {"1*2*3", "$times($times(1, 2), 3)"},
                {"b1 ==> b2 ==> b3", "$imp(b1, $imp(b2, b3))"},
        };
    }

    public String[][] parametersForTestSchematic() {
        return new String[][] {
            { "?x+3", "$plus(?x, 3)" },
            { "_*5", "$times(_, 5)" },
            { "1 * ... x+y ...", "$times(1, (... $add(x, y) ...))" },
            { "if ?x then ?x else 5", "$ite<int>(?x, ?x, 5)" },
            { "forall i:int :: ?phi", "forall i:int :: ?phi" },
            { "args(__)", "args(_, _, _)" },
            { "args(__, ?x)", "args(_, _, ?x)" },
            { "args(__, ?x, ?y)", "args(_, ?x, ?y)" },
            { "args(?y, __)", "args(?y, _, _)" },
            { "args(?x, ?y, __)", "args(?x, ?y, _)" },
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
            { "forall x,y,z:int :: unknown", "" },  // no more bound vars after this
            { "f(b1)", "Unexpected argument sort" },
            { "if true then b1 else i1", "Unexpected argument sort" },
            {"a.Length0", "Elements of type 'array' have only the 'Length' property"},
            // revealed wrong error message:
            {"a2.Length", "Elements of type 'array2' have only the 'Length0' and 'Length1' properties"},
            {"a2.Length2", "Elements of type 'array2' have only the 'Length0' and 'Length1' properties"},
            {"i1.Length", "Unsupported sort for 'Length': int"},
            {"a2[0]", "Access to 'array2' requires two index arguments"},
            {"a[0,1]", "Access to 'array' requires one index argument"},
            {"i1[i1]", "Unsupported array sort: int" },
            { "args(__, ?x, ?y, ?z)", "Illegal number of arguments" },
            { "args(?x, ?y, ?z, __)", "Illegal number of arguments" },
        };
    }

    @Before
    public void setupTable() {
        Collection<FunctionSymbol> map = new ArrayList<>();
        map.add(new FunctionSymbol("i1", Sort.INT));
        map.add(new FunctionSymbol("i2", Sort.INT));
        map.add(new FunctionSymbol("i3", Sort.INT));
        map.add(new FunctionSymbol("b1", Sort.BOOL));
        map.add(new FunctionSymbol("b2", Sort.BOOL));
        map.add(new FunctionSymbol("b3", Sort.BOOL));
        map.add(new FunctionSymbol("a", Sort.get("array", Sort.INT)));
        map.add(new FunctionSymbol("a2", Sort.get("array2", Sort.INT)));
        map.add(new FunctionSymbol("f", Sort.INT, Sort.INT));
        map.add(new FunctionSymbol("c", Sort.getClassSort("C")));
        map.add(new FunctionSymbol("c2", Sort.getClassSort("C")));
        map.add(new FunctionSymbol("args", Sort.INT, Sort.INT, Sort.BOOL, Sort.BOOL));
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

        DafnyTree t = parse(input, true);
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

    @Test @Parameters
    public void testSchematic(String input, String expected) throws Exception {
        assertNotNull(symbTable);

        TreeTermTranslator ttt = new TreeTermTranslator(symbTable);

        DafnyTree t = parse(input, true);
        Term term = ttt.build(t);

        assertEquals(expected, term.toString());
        assertEquals(0, ttt.countBoundVars());
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

        TreeTermTranslator ttt = new TreeTermTranslator(symbTable);

        Term result = ttt.build(assignments, post);

        Term expected = TermParser.parse(symbTable,
                "let heap := $store<C,int>($heap, this, C$$field, "
                + "$plus($select<C, int>($heap, this, C$$field), 1)) :: "
                + "let heap := $store<D, D>(heap, d, D$$field, null) :: "
                + "$select<C, int>(heap, this, C$$field) > 0");

        assertEquals(expected.toString(), result.toString());
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

    @Test
    public void testWildcard() throws Exception {
        TreeTermTranslator ttt = new TreeTermTranslator(symbTable);

        DafnyTree wc = new DafnyTree(DafnyParser.WILDCARD, "*");
        wc.setExpressionType(ASTUtil.id("int"));

        Term res1 = ttt.build(wc);
        Term res2 = ttt.build(wc);

        assertEquals("unknown_1", res1.toString());
        assertEquals("unknown_2", res2.toString());
    }

    @Test
    public void testWildcardWithHint() throws Exception {
        symbTable.addFunctionSymbol(new FunctionSymbol("knownvar_1", Sort.INT));
        TreeTermTranslator ttt = new TreeTermTranslator(symbTable);

        DafnyTree wc = new DafnyTree(DafnyParser.WILDCARD, "*");
        wc.setExpressionType(ASTUtil.id("int"));
        wc.addChild(ASTUtil.id("knownvar_1"));

        Term res1 = ttt.build(wc);
        Term res2 = ttt.build(wc);

        assertEquals("knownvar_1", res1.toString());
        assertEquals("knownvar_1", res2.toString());
    }

    @Test
    public void testThis() throws Exception {
        symbTable.addFunctionSymbol(new FunctionSymbol("this", Sort.get("C")));
        DafnyTree tree = DafnyFileParser.parse(TestUtil.toStream("class C { var f : int; "
                + "method m() returns (r : C) { r := this; } }"));
        Project p = TestUtil.mockProject(tree);

        TreeTermTranslator ttt = new TreeTermTranslator(symbTable);
        DafnyTree thisRef = p.getClass("C").getMethod("m").getBody().getChild(0).getChild(1);
        Term result = ttt.build(thisRef);

        assertEquals("this", result.toString());
    }

    @Test
    public void testFieldAccess() throws Exception {
        symbTable.addFunctionSymbol(new FunctionSymbol("this", Sort.get("C")));
        symbTable.addFunctionSymbol(new FunctionSymbol("field$C$f",
                Sort.get("field", Sort.get("C"), Sort.INT)));
        DafnyTree tree = DafnyFileParser.parse(TestUtil.toStream("class C { var f : int; "
                + "method m() returns (r : int) { r := this.f; } }"));
        Project p = TestUtil.mockProject(tree);

        TreeTermTranslator ttt = new TreeTermTranslator(symbTable);
        DafnyTree fieldRef = p.getClass("C").getMethod("m").getBody().getChild(0).getChild(1);
        Term result = ttt.build(fieldRef);

        assertEquals("$select<C,int>($heap, this, field$C$f)", result.toString());

    }

    public String[][] parametersForTestSequentTranslation() {
        return new String[][]{
                {"b1 ==> b2, b2 ==> b3 |- b1 && b2, b2&&b3",
                        "[$imp(b1, b2), $imp(b2, b3)] ==> [$and(b1, b2), $and(b2, b3)]"}
        };
    }

    @Test
    @Parameters
    public void testSequentTranslation(String seq, String exp) throws Exception {
        TermParser tp = new TermParser(symbTable);
        Sequent sequent = tp.parseSequent(seq);
        System.out.println("tp = " + sequent);
        Assert.assertEquals("First sequent ", exp, sequent.toString());
    }
}
