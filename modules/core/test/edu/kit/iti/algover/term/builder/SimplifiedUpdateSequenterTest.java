/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.term.builder;

/*
method m(p : int, m : set<object>) returns (r:int)
  requires p > 0
  ensures r > 0
  modifies m
{
  var local : int;
  local := p;
  if local > 0
  {
     r := local;
  } else {
     r := -local;
  }
}
 */

import edu.kit.iti.algover.dafnystructures.DafnyMethod;
import edu.kit.iti.algover.data.BuiltinSymbols;
import edu.kit.iti.algover.data.SymbolTable;
import edu.kit.iti.algover.parser.DafnyTree;
import edu.kit.iti.algover.parser.ParserTest;
import edu.kit.iti.algover.project.Project;
import edu.kit.iti.algover.proof.ProofFormula;
import edu.kit.iti.algover.symbex.AssertionElement.AssertionType;
import edu.kit.iti.algover.symbex.Symbex;
import edu.kit.iti.algover.symbex.SymbexPath;
import edu.kit.iti.algover.term.Sequent;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.term.parser.TermParser;
import edu.kit.iti.algover.util.TestUtil;
import junitparams.JUnitParamsRunner;
import junitparams.Parameters;
import org.junit.Test;
import org.junit.runner.RunWith;

import java.io.InputStream;
import java.util.Collections;
import java.util.List;

import static org.junit.Assert.assertEquals;

@RunWith(JUnitParamsRunner.class)
public class SimplifiedUpdateSequenterTest extends SequenterTest {

    @Override
    protected PVCSequenter makeSequenter() {
        return new SimplifiedUpdateSequenter();
    }

    @Override
    protected String expectedAntecedent(String pathIdentifier) {
        return "[$gt(p, 0), (let local := p :: $gt(local, 0))]";
    }

    @Override
    protected String expectedSuccedent(String pathIdentifier) {
        return "[(let local := p :: (let r := local :: $gt(r, 0)))]";
    }

    public String[][] parametersForTestIrrelevantLets() {
        return new String[][] {
                { "let x,x2,x3 := 1,2,3 :: let x,y := 2,x :: let z := y :: y==2+x2+z",
                        "let x,x2 := 1,2 :: let y := x :: let z := y :: y==2+x2+z" },
                { "let x := 1 :: let y := 2 :: x>0",
                        "let x := 1 :: x>0"},
                { "let x := 1 :: let x := 1 + x :: x > 0",
                  "let x := 1 :: let x := 1 + x :: x > 0" },
                // from a bug:
                { "let x:=1 :: let y:=x :: true", "true"},
                // from a heap treatment bug:
                { "(let $heap := $array_store<int>($heap, null, 1, 1) :: " +
                    " let x := 42 :: " +
                    " let $heap := $array_store<int>($heap, null, 2, 1) :: " +
                    "$array_select<int>($heap, null, 2) == 0)",
                  "(let $heap := $array_store<int>($heap, null, 1, 1) :: " +
                    " let $heap := $array_store<int>($heap, null, 2, 1) :: " +
                    "$array_select<int>($heap, null, 2) == 0)" },
        };
    }

    // revealed a problem in the post processing
    @Test @Parameters
    public void testIrrelevantLets(String inputStr, String expectedStr) throws Exception {

        // Only test the postprocessing process. ....

        SymbolTable st = new BuiltinSymbols();
        Term t = TermParser.parse(st, inputStr);
        ProofFormula profForm = new ProofFormula(t);

        SimplifiedUpdateSequenter sus = new SimplifiedUpdateSequenter();
        ProofFormula actual = sus.postProcess(profForm, Collections.emptyMap());
        Term expected = TermParser.parse(st, expectedStr);

        assertEquals(expected, actual.getTerm());

    }

    // revealed a bug in simplification
    @Test
    public void testCrossClass() throws Exception {

        InputStream stream = getClass().getResourceAsStream("../../symbex/crossClass.dfy");
        DafnyTree fileTree = ParserTest.parseFile(stream);

        Project project = TestUtil.mockProject(fileTree);
        Symbex symbex = new Symbex();
        DafnyMethod method = project.getClass("C").getMethod("setD");
        List<SymbexPath> results = symbex.symbolicExecution(method.getRepresentation());
        SymbexPath path = results.get(0).split().get(0);
        assertEquals(AssertionType.POST, path.getCommonProofObligationType());

        PVCSequenter sequenter = makeSequenter();
        SymbolTable table = makeTable(method, project);
        Sequent sequent = sequenter.translate(path, table, null);

        // path.getAssignmentHistory().forEach(x -> System.out.println(x.toStringTree()));
        // (ASSIGN $mod (SETEX this x))
        // (ASSIGN $decr 0)
        // (ASSIGN $oldheap $heap)
        // (:= (FIELD_ACCESS this d) x)
        // (:= d x)
        // (:= (FIELD_ACCESS x c) this)

        assertEquals("[PreCond]: $not($eq<D>(x, null)) |- " +
                "[Assertion]: (let $heap := $store<C,D>($heap, this, C$$d, x) :: " +
                "(let $heap := $store<C,D>($heap, this, C$$d, x) :: " +
                "(let $heap := $store<D,C>($heap, x, D$$c, this) :: " +
                "$eq<D>($select<C,D>($heap, this, C$$d), x))))", sequent.toString());
    }

    protected void checkSequentWithOld(SymbolTable table, Sequent sequent) throws Exception {

        assertEquals("|- [Assertion]: (let $oldheap := $heap :: " +
                "(let $heap := $store<C,int>($heap, c, C$$i, 0) :: " +
                "(let $heap := $store<C,int>($heap, c, C$$i, " +
                "$plus((let $heap := $oldheap :: $select<C,int>($heap, c, C$$i)), 1)) :: " +
                "$eq<int>($select<C,int>($heap, c, C$$i), $plus((let $heap := $oldheap :: " +
                "$select<C,int>($heap, c, C$$i)), 1)))))", sequent.toString());

        Term inlined = LetInlineVisitor.inline(sequent.getSuccedent().get(0).getTerm());
        assertEquals(TermParser.parse(table, "c.i@$heap[c.i:=0][c.i:=c.i@$heap+1] == c.i + 1"), inlined);
    }

}
