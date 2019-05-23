/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.term.builder;

import static org.junit.Assert.assertEquals;

import java.io.InputStream;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import edu.kit.iti.algover.data.SymbolTable;
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
        return "[$gt(p, 0), (let $mod, $decr, $oldheap, local := m, $plus(p, 1), $heap, p :: $gt(local, 0))]";
    }

    // for the normal upd-sequenter "[(let $mod := m :: (let local := p :: (let r := local :: $gt(r, 0))))]";
    protected String expectedSuccedent(String string) {
        return "[(let $mod, $decr, $oldheap, local, r, $heap := m, $plus(p, 1), $heap, p, p, $heap :: $gt(r, 0))]";
    }

    @Override
    protected PVCSequenter makeSequenter() {
        return new ParallelUpdateSequenter();
    }

    protected void checkSequentWithOld(SymbolTable table, Sequent sequent) throws Exception {

        assertEquals("|- (let $mod, $decr, $oldheap, $heap := " +
                "$empty, 0, $heap, $store<C,int>($heap, c, C$$i, $plus($select<C,int>($heap, c, C$$i), 1)) :: " +
                "$eq<int>($select<C,int>($heap, c, C$$i), " +
                "$plus((let $heap := $oldheap :: $select<C,int>($heap, c, C$$i)), 1)))", sequent.toString());

        Term inlined = LetInlineVisitor.inline(sequent.getSuccedent().get(0).getTerm());
        assertEquals(TermParser.parse(table, "c.i@$heap[c.i:=c.i+1] == c.i + 1"), inlined);
    }
}
