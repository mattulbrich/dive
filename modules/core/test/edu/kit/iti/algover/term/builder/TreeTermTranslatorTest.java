/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.term.builder;

import edu.kit.iti.algover.data.BuiltinSymbols;
import edu.kit.iti.algover.data.MapSymbolTable;
import edu.kit.iti.algover.parser.DafnyException;
import edu.kit.iti.algover.parser.DafnyFileParser;
import edu.kit.iti.algover.parser.DafnyLexer;
import edu.kit.iti.algover.parser.DafnyParser;
import edu.kit.iti.algover.parser.DafnyParser.expression_only_return;
import edu.kit.iti.algover.parser.DafnyParserException;
import edu.kit.iti.algover.parser.DafnyTree;
import edu.kit.iti.algover.project.Project;
import edu.kit.iti.algover.term.*;
import edu.kit.iti.algover.term.parser.TermParser;
import edu.kit.iti.algover.util.ASTUtil;
import edu.kit.iti.algover.util.Pair;
import edu.kit.iti.algover.util.TestUtil;
import junitparams.JUnitParamsRunner;
import junitparams.Parameters;
import org.antlr.runtime.ANTLRStringStream;
import org.antlr.runtime.CommonTokenStream;
import org.antlr.runtime.RecognitionException;
import org.junit.Assert;
import org.junit.Before;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.ExpectedException;
import org.junit.runner.RunWith;

import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import static org.junit.Assert.*;


@RunWith(JUnitParamsRunner.class)
public class TreeTermTranslatorTest {

    @Rule
    public ExpectedException thrown = ExpectedException.none();

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

            { "!b1", "$not(b1)" },
            { "-i1", "$neg(i1)" },

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

            { "c == null", "$eq<C>(c, null)" },
            { "c == c2", "$eq<C>(c, c2)" },
            { "c == d", "$eq<object>(c, d)" },
            { "let c := null :: null == c",
                "(let c := null :: $eq<null>(null, c))" },

            // endless expressions
            { "1 + if b1 then 1 else 0", "$plus(1, $ite<int>(b1, 1, 0))" },
            { "if b1 then 1 else 0 + 1", "$ite<int>(b1, 1, $plus(0, 1))" },
            { "true && forall i:int :: i==i", "$and(true, (forall i:int :: $eq<int>(i, i)))" },
            { "(if true then 1 else 0) + (if true then 1 else 0)",
              "$plus($ite<int>(true, 1, 0), $ite<int>(true, 1, 0))" },

            // Heap accesses
            {"a[0]", "$array_select<int>($heap, a, 0)"},
            {"a[0]+a[0]", "$plus($array_select<int>($heap, a, 0), $array_select<int>($heap, a, 0))"},
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
            { "-1", "$neg(1)" },

            // Associativity
            { "1+2-3", "$minus($plus(1, 2), 3)" },
            { "1*2*3", "$times($times(1, 2), 3)" },
            { "b1 ==> b2 ==> b3", "$imp(b1, $imp(b2, b3))" },

            // Heap accesses
            { "c.f", "$select<C,int>($heap, c, C$$f)" },
            { "c.f", "$select<C,int>($heap, c, C$$f)" },
            { "c.f@loopHeap", "$select<C,int>(loopHeap, c, C$$f)" },
            { "c.fct(1)", "C$$fct($heap, c, 1)"},
            { "c.fct(1)@loopHeap", "C$$fct(loopHeap, c, 1)"},

            // Heap updates
            { "$heap[c.f := 1]", "$store<C,int>($heap, c, C$$f, 1)" },
            { "$heap[$anon(mod, loopHeap)]", "$anon($heap, mod, loopHeap)" },
            { "$heap[$create(c)]", "$create($heap, c)" },

            // Set, Seqs and cardinalities
            { "|mod|", "$set_card<object>(mod)" },
            { "|iseq|", "$seq_len<int>(iseq)" },
            { "{1,2,3}", "$set_add<int>(3, $set_add<int>(2, $set_add<int>(1, $empty)))" },
            { "[1,2,3]", "$seq_cons<int>(3, $seq_cons<int>(2, $seq_cons<int>(1, $seq_empty)))" },
            { "iseq + iseq", "$seq_concat<int>(iseq, iseq)" },
            { "mod * mod", "$intersect<object>(mod, mod)" },
            { "mod + mod", "$union<object>(mod, mod)" },
            { "cseq + dseq", "$seq_concat<object>(cseq, dseq)" },
            { "{}", "$empty" },
            { "{} == {1}", "$eq<set<int>>($empty, $set_add<int>(1, $empty))" },
            { "[]", "$seq_empty" },
            { "[] == [1]", "$eq<seq<int>>($seq_empty, $seq_cons<int>(1, $seq_empty))" },
        };
    }

    public String[][] parametersForTestSchematic() {
        return new String[][] {
            { "?x+3", "$plus(?x, 3)" },
            { "3+?x", "$plus(3, ?x)" },
            { "5*_", "$times(5, _)" },
            { "_*5", "$times(_, 5)" },
            { "_+_(:int)", "$plus(_, _)" },
            { "?x(:set<object>) + ?y", "$union<object>(?x, ?y)" },
            { "(?a: ?x+3)", "(?a: $plus(?x, 3))" },
            { "1 * ... i1+?x ...", "$times(1, (... $plus(i1, ?x) ...))" },
            { "if ?x then ?x else 5", "$ite<int>(?x, ?x, 5)" },
            { "forall i:int :: ?phi", "(forall i:int :: ?phi)" },
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
            { "b1 == i1", "No common supertype for bool and int" },
            { "let x,y:=1 :: y", "Mismatched assignments in let expression:" },
            { "let x:=1 :: unknown", "" },  // no more bound vars after this
            { "forall x:int :: unknown", "" },  // no more bound vars after this
            { "forall x,y,z:int :: unknown", "" },  // no more bound vars after this
            { "f(b1)", "Unexpected argument sort" },
            { "if true then b1 else i1", "No common supertype for bool and int" },
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
            { "c.f@1", "heap suffixes must specify a heap" },
            { "c.g", "Field g not found in class C" },
            { "1.f", "field access only possible for class sorts" },
            { "1@loopHeap", "heap suffixes are only allowed for heap select terms" },
            { "b1[c.f:=1]", "Heap updates must be applied to heaps" },
            { "loopHeap[c := c]", "Heap updates must modify a heap location" },
            { "loopHeap[c.f := true]", "Unexpected argument sort for argument 4 to $store" },
            { "iseq + mod", "No common supertype for seq<int> and set<object>" },
            { "true + true", "'+' is not supported for these arguments" },
            { "c == 1", "No common supertype for C and int" },
        };
    }

    @Before
    public void setupTable() throws DafnyParserException, RecognitionException, IOException, DafnyException {
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
        map.add(new FunctionSymbol("d", Sort.getClassSort("D")));
        map.add(new FunctionSymbol("c2", Sort.getClassSort("C")));
        map.add(new FunctionSymbol("args", Sort.INT, Sort.INT, Sort.BOOL, Sort.BOOL));
        map.add(new FunctionSymbol("loopHeap", Sort.HEAP));
        map.add(new FunctionSymbol("mod", Sort.get("set", Sort.OBJECT)));
        map.add(new FunctionSymbol("iseq", Sort.get("seq", Sort.INT)));
        map.add(new FunctionSymbol("cseq", Sort.get("seq", Sort.getClassSort("C"))));
        map.add(new FunctionSymbol("dseq", Sort.get("seq", Sort.getClassSort("D"))));
        Project p = TestUtil.mockProject("class C { var f: int; function fct(i:int): int {0} }");
        map.addAll(p.getAllDeclaredSymbols());
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
        assertUniqueFunctionSymbols(t);
    }

    @Test @Parameters
    public void failingParser(String input, String errMsg) throws Exception {
        assertNotNull(symbTable);

        TreeTermTranslator ttt = new TreeTermTranslator(symbTable);

        DafnyTree t = parse(input, true);

        thrown.expect(TermBuildException.class);
        thrown.expectMessage(errMsg);

        try {
            ttt.build(t);
        } finally {
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

        assertUniqueFunctionSymbols(t);
    }

    /**
     * create terms from tree twice, ensuring that no symbol is created twice!
     */
    private void assertUniqueFunctionSymbols(DafnyTree tree) throws Exception {
        TreeTermTranslator ttt = new TreeTermTranslator(symbTable);
        Term term = ttt.build(tree);
        Term term2 = ttt.build(tree);
        Map<String, FunctionSymbol> found = new HashMap<>();
        assertUniqueFunctionSymbols(found, term);
        assertUniqueFunctionSymbols(found, term2);
    }

    private void assertUniqueFunctionSymbols(Map<String, FunctionSymbol> found, Term term) {
        if (term instanceof ApplTerm) {
            ApplTerm applTerm = (ApplTerm) term;
            FunctionSymbol fs = applTerm.getFunctionSymbol();
            String key = fs.getName();
            FunctionSymbol cached = found.get(key);
            if(cached != null) {
                assertSame("Symbols must be unique: " + key, cached, fs);
            } else {
                found.put(key, fs);
            }
        }
        for (Term t : term.getSubterms()) {
            assertUniqueFunctionSymbols(found, t);
        }
    }

    // Moved to TreeAssignmentTranslatorTest
//    // revealed a bug
//    @Test
//    public void letCascade() throws Exception {
//
//        DafnyTree tree = DafnyFileParser.parse(getClass().getResourceAsStream("proj1/treeTransTest.dfy"));
//        Project p = TestUtil.mockProject(tree);
//
//        DafnyTree method = p.getMethod("m").getRepresentation();
//        DafnyTree block = method.getFirstChildWithType(DafnyParser.BLOCK);
//
//        DafnyTree post = method.getFirstChildWithType(DafnyParser.ENSURES).getLastChild();
//
//        ImmutableList<DafnyTree> assignments =
//                ImmutableList.<DafnyTree>from(block.getChildren().subList(1, block.getChildCount()));
//
//        assertNotNull(symbTable);
//
//        TreeTermTranslator ttt = new TreeTermTranslator(symbTable);
//
//        Term result = ttt.build(assignments, post);
//
//        Term expected = TermParser.parse(symbTable,
//                "let x:=5 :: let x:=i1+x :: let i2 := i1*2 :: i2 > 0");
//
//        assertEquals(expected, result);
//    }
//
//    @Test
//    public void letCascadeHeap() throws Exception {
//
//        symbTable.addFunctionSymbol(new FunctionSymbol("this", Sort.getClassSort("C")));
//        symbTable.addFunctionSymbol(new FunctionSymbol("d", Sort.getClassSort("D")));
//        symbTable.addFunctionSymbol(new FunctionSymbol("C$$field", Sort.get("field", Sort.getClassSort("C"), Sort.INT)));
//        symbTable.addFunctionSymbol(new FunctionSymbol("D$$field", Sort.get("field", Sort.getClassSort("D"), Sort.getClassSort("D"))));
//
//        DafnyTree tree = DafnyFileParser.parse(getClass().getResourceAsStream("proj1/treeTransTest.dfy"));
//        Project p = TestUtil.mockProject(tree);
//
//        DafnyTree method = p.getClass("C").getMethod("n").getRepresentation();
//        DafnyTree block = method.getFirstChildWithType(DafnyParser.BLOCK);
//
//        DafnyTree post = method.getFirstChildWithType(DafnyParser.ENSURES).getLastChild();
//
//        ImmutableList<DafnyTree> assignments =
//                ImmutableList.<DafnyTree>from(block.getChildren());
//
//        assertNotNull(symbTable);
//
//        TreeTermTranslator ttt = new TreeTermTranslator(symbTable);
//
//        Term result = ttt.build(assignments, post);
//
//        Term expected = TermParser.parse(symbTable,
//                "let heap := $store<C,int>($heap, this, C$$field, "
//                + "$plus($select<C, int>($heap, this, C$$field), 1)) :: "
//                + "let heap := $store<D, D>(heap, d, D$$field, null) :: "
//                + "$select<C, int>(heap, this, C$$field) > 0");
//
//        assertEquals(expected.toString(), result.toString());
//    }
//
//    @Test
//    public void letCascadeSeq() throws Exception {
//        symbTable.addFunctionSymbol(new FunctionSymbol("this", Sort.getClassSort("Seq")));
//        symbTable.addFunctionSymbol(new FunctionSymbol("Seq$$fsq",
//                Sort.get("field", Sort.getClassSort("Seq"), Sort.get("seq", Sort.INT))));
//        symbTable.addFunctionSymbol(new FunctionSymbol("sq", Sort.get("seq", Sort.INT)));
//
//        DafnyTree tree = DafnyFileParser.parse(getClass().getResourceAsStream("proj1/treeTransTest.dfy"));
//        Project p = TestUtil.mockProject(tree);
//
//        DafnyTree method = p.getClass("Seq").getMethod("s").getRepresentation();
//        DafnyTree block = method.getFirstChildWithType(DafnyParser.BLOCK);
//
//        ImmutableList<DafnyTree> assignments =
//                ImmutableList.<DafnyTree>from(block.getChildren()).
//                        filter(x -> x.getType() == DafnyParser.ASSIGN);
//
//        DafnyTree post = method.getFirstChildWithType(DafnyParser.ENSURES).getLastChild();
//
//        TreeTermTranslator ttt = new TreeTermTranslator(symbTable);
//
//        Term result = ttt.build(assignments, post);
//
//        Term expected = TermParser.parse(symbTable,
//                "let sq := $seq_upd<int>(sq, 0, 2) :: " +
//                        "let heap := $store<Seq, seq<int>>($heap, this, " +
//                        "Seq$$fsq, $seq_upd<int>($select<Seq,seq<int>>($heap, this, Seq$$fsq), 1, 3)) :: " +
//                        "let heap := $store<Seq,seq<int>>(heap, this, " +
//                        "Seq$$fsq, $seq_upd<int>($select<Seq, seq<int>>($heap, this, Seq$$fsq), 2, 4)) :: " +
//                        "true");
//
//        assertEquals(expected.toString(), result.toString());
//    }

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
        DafnyTree tree = DafnyFileParser.parse(TestUtil.toStream("class C { var f : int; "
                + "method m() returns (r : int) { r := this.f; } }"));
        Project p = TestUtil.mockProject(tree);

        TreeTermTranslator ttt = new TreeTermTranslator(symbTable);
        DafnyTree fieldRef = p.getClass("C").getMethod("m").getBody().getChild(0).getChild(1);
        Term result = ttt.build(fieldRef);

        assertEquals("$select<C,int>($heap, this, C$$f)", result.toString());

    }

    public String[][] parametersForTestSequentTranslation() {
        return new String[][]{
                {"b1 ==> b2, b2 ==> b3 |- b1 && b2, b2&&b3",
                        "$imp(b1, b2), $imp(b2, b3) |- $and(b1, b2), $and(b2, b3)"}
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

    @Test
    public void testSubst() throws Exception {
        symbTable.addFunctionSymbol(new FunctionSymbol("obj", Sort.get("C")));
        symbTable.addFunctionSymbol(new FunctionSymbol("this", Sort.get("C")));
        symbTable.addFunctionSymbol(new FunctionSymbol("ff", Sort.INT, Sort.INT, Sort.INT));

        DafnyTree tree = DafnyFileParser.parse(TestUtil.toStream("class C { var f : int; "
                + "method m(c : C) returns (r : int) { r := this.f + c.f + r; } }"));
        Project p = TestUtil.mockProject(tree);

        DafnyTree add = p.getClass("C").getMethod("m").getBody().getChild(0).getChild(1);
        List<Pair<String, DafnyTree>> substs = Arrays.asList(
                new Pair<>("this", ASTUtil.id("obj")),
                new Pair<>("c", ASTUtil._this()),
                new Pair<>("r", ASTUtil.call("ff", ASTUtil.intLiteral(2), ASTUtil.intLiteral(3)))
                );
        DafnyTree subst = ASTUtil.letCascade(substs, add);
        TreeTermTranslator ttt = new TreeTermTranslator(symbTable);
        Term result = ttt.build(subst);
        Term expected = TermParser.parse(symbTable, "let this,c,r := obj,this,ff(2,3) :: this.f + c.f + r");

        assertEquals(expected, result);
    }

}
