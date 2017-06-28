/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.term.builder;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.fail;

import java.io.ByteArrayInputStream;
import java.io.File;
import java.util.ArrayList;
import java.util.Collection;

import org.antlr.runtime.ANTLRStringStream;
import org.antlr.runtime.CommonTokenStream;
import org.antlr.runtime.RecognitionException;
import org.junit.Before;
import org.junit.Test;
import org.junit.runner.RunWith;

import edu.kit.iti.algover.data.BuiltinSymbols;
import edu.kit.iti.algover.data.MapSymbolTable;
import edu.kit.iti.algover.facade.ProjectFacade;
import edu.kit.iti.algover.parser.DafnyFileParser;
import edu.kit.iti.algover.parser.DafnyLexer;
import edu.kit.iti.algover.parser.DafnyParser;
import edu.kit.iti.algover.parser.DafnyParser.expression_only_return;
import edu.kit.iti.algover.parser.DafnyTree;
import edu.kit.iti.algover.project.Project;
import edu.kit.iti.algover.term.FunctionSymbol;
import edu.kit.iti.algover.term.Sort;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.term.parser.TermParser;
import edu.kit.iti.algover.util.ImmutableList;
import junitparams.JUnitParamsRunner;
import junitparams.Parameters;


@RunWith(JUnitParamsRunner.class)
public class TreeTermTranslatorTest {

    private static final File FILE = new File("modules/core/test-res/edu/kit/iti/algover/term/builder/proj1");

    public String[][] parametersForTestTermTranslation() {
        return new String[][] {
            { "i1 + i2*i3", "$plus(i1, $times(i2, i3))" },
            // revealed bug:
            { "i1 == i2*i3", "$eq[int](i1, $times(i2, i3))" },
            { "a.Length", "$len0(a)" },
            //                { "a2.Length0", "$len0(a)" },
            //                { "a2.Length1", "$len1(a)" },
            // no 2-dim arrays for now

            // for coverage:
            { "i1 > i2", "$gt(i1, i2)" },
            { "i1 >= i2", "$ge(i1, i2)" },
            { "i1 < i2", "$lt(i1, i2)" },
            { "i1 <= i2", "$le(i1, i2)" },
            { "i1 == i2", "$eq[int](i1, i2)" },
            { "b1 == b2", "$eq[bool](b1, b2)" },
            { "i1 != i2", "$not($eq[int](i1, i2))" },
            { "i1 - 1 - 2", "$minus($minus(i1, 1), 2)" },

            { "false && true", "$and(false, true)" },
            { "b1 || b2 ==> b3", "$imp($or(b1, b2), b3)" },
            { "forall x:int :: exists y:int :: x > y",
            "(forall x:int :: (exists y:int :: $gt(x, y)))" },
            { "let x := 3 :: x > i1", "(let x := 3 :: $gt(x, i1))" },
            { "$plus(1, 2)", "$plus(1, 2)" },
        };
    }

    public String[][] parametersForFailingParser() {
        return new String[][] {
            { "unknownFunction(1)" },
            { "unknownIdentifier" },
            { "b1 == i1" },
            { "let x,y:=1 :: y" },
            { "let x:=1 :: unknown" },  // no more bound vars after this
            { "forall x:int :: unknown" },  // no more bound vars after this
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
        map.add(new FunctionSymbol("a", new Sort("array1")));
        map.add(new FunctionSymbol("a2", new Sort("array2")));
        symbTable = new MapSymbolTable(new BuiltinSymbols(), map);
    }

    @Test @Parameters
    public void testTermTranslation(String input, String expected) throws Exception {
        assertNotNull(symbTable);

        TreeTermTranslator ttt = new TreeTermTranslator(symbTable);

        DafnyTree t = parse(input);
        Term term = ttt.build(t);

        assertEquals(expected, term.toString());
    }

    @Test @Parameters
    public void failingParser(String input) throws Exception {
        assertNotNull(symbTable);

        TreeTermTranslator ttt = new TreeTermTranslator(symbTable);

        DafnyTree t = parse(input);
        try {
            ttt.build(t);
            fail("Should not reach this here");
        } catch (TermBuildException e) {
//            e.printStackTrace();
            assertEquals(0, ttt.countBoundedVars());
        }

    }

    @Test
    public void parametersForLetCascade() throws Exception {

        Project p = ProjectFacade.getInstance().buildProject(FILE);

        DafnyTree method = p.getMethod("m").getRepresentation();
        DafnyTree block = method.getFirstChildWithType(DafnyParser.BLOCK);

        DafnyTree post = method.getFirstChildWithType(DafnyParser.ENSURES).getLastChild();

        ImmutableList<DafnyTree> assignments =
                ImmutableList.<DafnyTree>from(block.getChild(1), block.getChild(2), block.getChild(3));

        assertNotNull(symbTable);

        TreeTermTranslator ttt = new TreeTermTranslator(symbTable);

        Term result = ttt.build(assignments, post);

        Term expected = TermParser.parse(symbTable,
                "let x:=5 :: let x:=i1+x :: let i2 := i1*2 :: i2 > 0");

        assertEquals(expected, result);
    }



}
