/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.term.builder;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

import java.io.InputStream;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import edu.kit.iti.algover.data.BuiltinSymbols;
import edu.kit.iti.algover.data.SymbolTable;
import edu.kit.iti.algover.parser.DafnyParserException;
import edu.kit.iti.algover.proof.ProofFormula;
import edu.kit.iti.algover.term.FunctionSymbol;
import edu.kit.iti.algover.term.Sort;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.term.parser.TermParser;
import org.junit.Ignore;
import org.junit.Test;

import edu.kit.iti.algover.dafnystructures.DafnyMethod;
import edu.kit.iti.algover.parser.DafnyException;
import edu.kit.iti.algover.parser.DafnyTree;
import edu.kit.iti.algover.parser.ParserTest;
import edu.kit.iti.algover.parser.ReferenceResolutionVisitor;
import edu.kit.iti.algover.parser.TypeResolution;
import edu.kit.iti.algover.project.Project;
import edu.kit.iti.algover.proof.PVC;
import edu.kit.iti.algover.rules.TermSelector;
import edu.kit.iti.algover.symbex.Symbex;
import edu.kit.iti.algover.symbex.SymbexPath;
import edu.kit.iti.algover.term.Sequent;
import edu.kit.iti.algover.util.TestUtil;

/**
 * This sequenter is a specialisation of an update sequenter.
 *
 * It aggregates all let-assignments into one single assigment
 *
 * <p> For example: In the term
 * <pre>
 *     let x,y,z:=1,2,3 :: let x,b:=x+1,y+1 :: x > 0
 * </pre>
 * the same variable is assigned several times. The result is
 * <pre>
 *     let x,y,z,b := 1+1,2,3,2+1 :: x > 0.
 * </pre>
 * Irrelevant assignments are NOT removed.
 *
 * @author Mattias Ulbrich
 */
public class ParallelUpdateSequenterTest extends SequenterTest {

    // for the normal upd-sequenter "[$gt(p, 0), (let $mod := m :: (let local := p :: $gt(local, 0)))]";
    protected String expectedAntecedent(String string) {
        return "[$gt(p, 0), (let $mod, $decr, $oldheap, local := $union<object>(m, $freshObjects($heap)), $plus(p, 1), $heap, p :: $gt(local, 0))]";
    }

    // for the normal upd-sequenter "[(let $mod := m :: (let local := p :: (let r := local :: $gt(r, 0))))]";
    protected String expectedSuccedent(String string) {
        return "[(let $mod, $decr, $oldheap, local, r, $heap := $union<object>(m, $freshObjects($heap)), $plus(p, 1), $heap, p, p, $heap :: $gt(r, 0))]";
    }

    @Override
    protected PVCSequenter makeSequenter() {
        return new ParallelUpdateSequenter();
    }

    protected void checkSequentWithOld(SymbolTable table, Sequent sequent) throws Exception {

        assertEquals("|- [Assertion]: (let $mod, $decr, $oldheap, $heap := " +
                "$freshObjects($heap), 0, $heap, $store<C,int>($store<C,int>($heap, c, C$$i, 0), " +
                "c, C$$i, $plus((let $heap := $heap :: $select<C,int>($heap, c, C$$i)), 1)) :: " +
                "$eq<int>($select<C,int>($heap, c, C$$i), $plus((let $heap := $oldheap :: $select<C,int>($heap, c, C$$i)), 1)))",
                sequent.toString());

        Term inlined = LetInlineVisitor.inline(sequent.getSuccedent().get(0).getTerm());
        assertEquals(TermParser.parse(table, "c.i@$heap[c.i:=0][c.i:=c.i+1] == c.i + 1"), inlined);
    }

    // from a nasty problem.
    // The heap update is needed before the old to trigger the problem.
    @Test
    public void testConflictingHeap() throws Exception {
        Project p = TestUtil.mockProject("class C { ghost var i:int; } " +
                "method m(c:C) ensures true { c.i := 0; var x := old(c.i); }");
        Symbex symbex = new Symbex();
        DafnyMethod method = p.getMethod("m");
        List<SymbexPath> results = symbex.symbolicExecution(method.getRepresentation());
        SymbexPath path = results.get(0);
        assertEquals("Post", path.getPathIdentifier());

        PVCSequenter sequenter = new UpdateSequenter();
        SymbolTable table = makeTable(method, p);
        Sequent sequent = sequenter.translate(path, table, null);

        ProofFormula formula = sequent.getSuccedent().get(0);
        assertTrue(AlphaNormalisation.isNormalised(formula.getTerm()));

        ProofFormula parallel = new ParallelUpdateSequenter().postProcess(formula, new HashMap<>());

        assertTrue(AlphaNormalisation.isNormalised(parallel.getTerm()));
    }

    @Test
    public void testConflictSmallLet() throws Exception {

        SymbolTable st = new BuiltinSymbols();
        st.addFunctionSymbol(new FunctionSymbol("x", Sort.INT));
        Term t = TermParser.parse(st, "(let y := x+1 :: (let x := x+x :: (let z := (let x := y :: x) :: true)))");
        assertTrue(AlphaNormalisation.isNormalised(t));
        ProofFormula pf = new ProofFormula(t);

        ProofFormula parallel = new ParallelUpdateSequenter().postProcess(pf, null);

        assertEquals("(let y, x, z := $plus(x, 1), $plus(x, x), (let x := $plus(x, 1) :: x) :: true)",
                parallel.getTerm().toString());

    }

    @Test
    public void testConflictSmallQuant() throws Exception {

        SymbolTable st = new BuiltinSymbols();
        st.addFunctionSymbol(new FunctionSymbol("x", Sort.INT));
        Term t = TermParser.parse(st, "(let y := x+1 :: (let x := x+x :: (let z := (forall x :: x > 0) :: true)))");
        assertTrue(AlphaNormalisation.isNormalised(t));
        ProofFormula pf = new ProofFormula(t);

        ProofFormula parallel = new ParallelUpdateSequenter().postProcess(pf, null);

        assertEquals("(let y, x, z := $plus(x, 1), $plus(x, x), (forall x:int :: $gt(x, 0)) :: true)",
                parallel.getTerm().toString());

    }
}

