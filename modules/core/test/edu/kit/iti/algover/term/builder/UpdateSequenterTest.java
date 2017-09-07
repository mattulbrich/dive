/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.term.builder;

import java.io.InputStream;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.junit.Ignore;
import org.junit.Test;

import edu.kit.iti.algover.dafnystructures.DafnyMethod;
import edu.kit.iti.algover.parser.DafnyTree;
import edu.kit.iti.algover.parser.ParserTest;
import edu.kit.iti.algover.project.Project;
import edu.kit.iti.algover.rules.TermSelector;
import edu.kit.iti.algover.symbex.Symbex;
import edu.kit.iti.algover.symbex.SymbexPath;
import edu.kit.iti.algover.term.Sequent;
import edu.kit.iti.algover.util.TestUtil;
import static org.junit.Assert.assertEquals;

public class UpdateSequenterTest extends SequenterTest {

    protected String expectedSuccedent(String string) {
        return "[(let $mod := m :: (let local := p :: (let r := local :: $gt(r, 0))))]";
    }

    protected String expectedAntecedent(String string) {
        return "[$gt(p, 0), (let $mod := m :: (let local := p :: $gt(local, 0)))]";
    }

    @Override
    protected PVCSequenter makeSequenter() {
        return new UpdateSequenter();
    }

    // used to debug a problem.
    @Test
    @Ignore
    public void testLetProblem1() throws Exception {
        InputStream is = getClass().getResourceAsStream("gcd.dfy");
        DafnyTree top = ParserTest.parseFile(is, null);
        // SyntacticSugarVistor.visit(top);
        Project p = TestUtil.mockProject(top);

        Symbex symbex = new Symbex();
        DafnyMethod method = p.getMethod("gcd");
        List<SymbexPath> results = symbex.symbolicExecution(method.getRepresentation());

        PVCSequenter sequenter = makeSequenter();
        for (SymbexPath paths : results) {
            for (SymbexPath path : paths.split()) {
                Sequent sequent = sequenter.translate(path, makeTable(method), null);
            }
        }
    }


}
