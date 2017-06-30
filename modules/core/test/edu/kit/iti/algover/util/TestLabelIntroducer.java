/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.util;


// import static org.junit.Assert.*;
import static org.junit.Assert.assertEquals;

import java.io.FileNotFoundException;
import java.io.IOException;
import java.net.URL;
import java.util.ArrayList;
import java.util.List;

import org.antlr.runtime.ANTLRStringStream;
import org.antlr.runtime.CommonTokenStream;
import org.antlr.runtime.RecognitionException;
import org.antlr.runtime.Token;
import org.junit.Test;

import edu.kit.iti.algover.parser.DafnyLexer;
import edu.kit.iti.algover.parser.DafnyParser;
import edu.kit.iti.algover.parser.DafnyParserException;
import edu.kit.iti.algover.parser.DafnyTree;
import edu.kit.iti.algover.parser.ParserTest;

public class TestLabelIntroducer {

    private static final boolean VERBOSE = false;

    @Test
    public void test() throws Exception {

        String filename = "labelTest.dfy";
        URL url = getClass().getResource(filename);
        if(url == null) {
            throw new FileNotFoundException(filename);
        }

        DafnyTree t = ParserTest.parseFile(url.openStream());

        if(VERBOSE) {
            System.out.println(Debug.prettyPrint(t.toStringTree()));
        }

        t.accept(new LabelIntroducer(), null);

        if(VERBOSE) {
            System.out.println(Debug.prettyPrint(t.toStringTree()));
        }

        {
            List<DafnyTree> trees = new ArrayList<>();
            collect(t, DafnyParser.INVARIANT, trees);
            List<String> labels =
                    Util.map(trees, x -> x.getFirstChildWithType(DafnyParser.LABEL).getChild(0).getText());
            assertEquals("[inv_2, withLabel, inv_3, inv_1, ass_2]", labels.toString());
        }
        {
            List<DafnyTree> trees = new ArrayList<>();
            collect(t, DafnyParser.REQUIRES, trees);
            List<String> labels =
                    Util.map(trees, x -> x.getFirstChildWithType(DafnyParser.LABEL).getChild(0).getText());
            assertEquals("[req_1, withReqLabel, req_2]", labels.toString());
        }
        {
            List<DafnyTree> trees = new ArrayList<>();
            collect(t, DafnyParser.ENSURES, trees);
            List<String> labels =
                    Util.map(trees, x -> x.getFirstChildWithType(DafnyParser.LABEL).getChild(0).getText());
            assertEquals("[ens_1, labelled, ens_2]", labels.toString());
        }
        {
            List<DafnyTree> trees = new ArrayList<>();
            collect(t, DafnyParser.ASSERT, trees);
            List<String> labels =
                    Util.map(trees, x -> x.getFirstChildWithType(DafnyParser.LABEL).getChild(0).getText());
            assertEquals("[ass_1, ass_3, assert_labelled, ass_4]", labels.toString());
        }
    }

    private void collect(DafnyTree t, int type, List<DafnyTree> result) {
        if(t.getType() == type) {
            result.add(t);
        }

        List<DafnyTree> children = t.getChildren();
        if(children != null) {
            for (DafnyTree child : children) {
                collect(child, type, result);
            }
        }
    }

    // help finding a bug
    @Test
    public void testInsertion() throws DafnyParserException, IOException, RecognitionException {
        String program = "method m()\n  requires R\n  ensures E\n{\n  assert A;\n  while W invariant I {} }";

        ANTLRStringStream input = new ANTLRStringStream(program);
        DafnyLexer lexer = new DafnyLexer(input);
        CommonTokenStream stream = new CommonTokenStream(lexer);
        List<? extends Token> tokens = stream.getTokens();

        DafnyParser parser = new DafnyParser(stream);
        parser.setTreeAdaptor(new DafnyTree.Adaptor());

        // launch the parser starting at rule r, get return object
        // better run the DafnyParser ... do not want to duplicate here
        DafnyTree tree = parser.program().getTree();

        LabelIntroducer li = new LabelIntroducer();
        tree.accept(li, null);


        StringBuilder sb = new StringBuilder();
        li.dumpWithInsertions(tokens, sb );

        String expected = "method m()\n  requires label req_1: R\n  ensures label ens_1: E\n"
                + "{\n  assert label ass_1: A;\n  while W invariant label inv_1: I {} }";

        assertEquals(expected, sb.toString());
    }

}
