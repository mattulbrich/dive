/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2016 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.term.builder;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotNull;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;

import org.antlr.runtime.ANTLRStringStream;
import org.antlr.runtime.CommonToken;
import org.antlr.runtime.CommonTokenStream;
import org.antlr.runtime.RecognitionException;
import org.junit.Before;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;

import edu.kit.iti.algover.data.BuiltinSymbols;
import edu.kit.iti.algover.data.MapSymbolTable;
import edu.kit.iti.algover.parser.DafnyLexer;
import edu.kit.iti.algover.parser.DafnyParser;
import edu.kit.iti.algover.parser.DafnyParser.expression_only_return;
import edu.kit.iti.algover.parser.DafnyTree;
import edu.kit.iti.algover.term.FunctionSymbol;
import edu.kit.iti.algover.term.Sort;
import edu.kit.iti.algover.term.Term;


@RunWith(Parameterized.class)
public class TreeTermTranslatorTest {

    @Parameters(name = "{0}")
    public static Iterable<Object[]> makeParameters() {
        return Arrays.asList(new Object[][] {
                { "i1 + i2*i3", "$plus(i1, $times(i2, i3))" },
                // revealed bug:
                { "i1 == i2*i3", "$eq_int(i1, $times(i2, i3))" },
                { "a.Length", "$len0(a)" },
//                { "a2.Length0", "$len0(a)" },
//                { "a2.Length1", "$len1(a)" },
                // no 2-dim arrays for now
        });
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
    private String input;
    private String output;

    public TreeTermTranslatorTest(Object input, Object output) {
        this.input = input.toString();
        this.output = output.toString();
    }

    @Before
    public void setupTable() {
        Collection<FunctionSymbol> map = new ArrayList<>();
        map.add(new FunctionSymbol("i1", Sort.INT));
        map.add(new FunctionSymbol("i2", Sort.INT));
        map.add(new FunctionSymbol("i3", Sort.INT));
        map.add(new FunctionSymbol("a", new Sort("array1")));
        map.add(new FunctionSymbol("a2", new Sort("array2")));
        symbTable = new MapSymbolTable(new BuiltinSymbols(), map);
    }

    @Test
    public void testTermTranslation() throws Exception {
        assertNotNull(symbTable);

        TreeTermTranslator ttt = new TreeTermTranslator(symbTable);

        DafnyTree t = parse(input);
        Term term = ttt.build(t);

        assertEquals(output, term.toString());
    }


}
