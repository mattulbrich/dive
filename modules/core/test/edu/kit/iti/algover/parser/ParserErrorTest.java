/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 *
 */

package edu.kit.iti.algover.parser;

import edu.kit.iti.algover.util.TestUtil;
import org.antlr.runtime.MismatchedSetException;
import org.hamcrest.BaseMatcher;
import org.hamcrest.Description;
import org.hamcrest.Matcher;
import org.junit.Ignore;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.ExpectedException;

import java.io.ByteArrayInputStream;
import java.io.IOException;

// does not only test parser, but also semantic analysis
public class ParserErrorTest {

    @Rule
    public ExpectedException thrown = ExpectedException.none();

    private Matcher<Throwable> treeReads(String s) {
        return new BaseMatcher<Throwable>() {
            @Override
            public boolean matches(Object o) {
                if (o instanceof DafnyException) {
                    DafnyException dex = (DafnyException) o;
                    DafnyTree tree = dex.getTree();
                    return (tree != null && tree.toStringTree().equals(s));
                } else {
                    return false;
                }
            }

            @Override
            public void describeTo(Description description) {
                description.appendText("dafny tree reads " + s);
            }

            @Override
            public void describeMismatch(Object o, Description description) {
                if (o instanceof DafnyException) {
                    DafnyException dex = (DafnyException) o;
                    DafnyTree tree = dex.getTree();
                    if(tree == null) {
                        description.appendText("has null tree");
                    } else {
                        description.appendText("has tree " + tree.toStringTree());
                    }
                } else {
                    description.appendText(" is not a DafnyException");
                }
            }
        };
    }

    // from an exception
    @Test
    public void unknownFunction() throws Exception {
        thrown.expect(DafnyException.class);
        thrown.expectMessage("Unknown method or function: unknownFunction");
        thrown.expect(treeReads("unknownFunction"));
        parse("method m() ensures unknownFunction() == 0 {}");
    }

    // from an exception
    @Test
    public void illegalArrayAccess() throws Exception {
        thrown.expect(DafnyException.class);
        thrown.expectMessage("Only arrays or sequences can be indexed");
        parse("method m(i:int) { i[0] := 0; }");
    }


    // correctness feature request.
    @Test @Ignore
    public void parametersMustNotBeModified() throws Exception {
        thrown.expect(DafnyException.class);
        thrown.expectMessage("");
        parse("method m(i:int) { i := 2; }");
    }

    // correctness feature request.
    @Test @Ignore
    public void parametersMustNotBeModified2() throws Exception {
        thrown.expect(DafnyException.class);
        thrown.expectMessage("");
        parse("method m(a:seq<int>) { a[0] := 0; }");
    }

    // After grammar change
    @Test
    public void wrongTypeVarDecl() throws Exception {
        thrown.expect(DafnyException.class);
        thrown.expectMessage("Assigning a value of type int to an entitity of type bool");
        parse("method m() { var b : bool := 42; }");
    }

    @Test @Ignore
    public void illegalReference() throws Exception {
        thrown.expect(DafnyException.class);
        thrown.expectMessage("Unknown identifier: m");
        parse("method m() returns (r: int) { m.o := 42; }");
    }

    @Test
    public void unknownField() throws Exception {
        thrown.expect(DafnyException.class);
        thrown.expectMessage("Unknown field mx in class C");
        parse("class C { method m() returns (r: int) { this.mx := 42; } }");
    }

    @Test @Ignore
    public void illegalThis() throws Exception {
        thrown.expect(DafnyException.class);
        thrown.expectMessage("xxxx");
        parse("method m() { if this == null {} }");
    }

    @Test
    public void assignToMethod() throws Exception {
        thrown.expect(DafnyParserException.class);
        thrown.expectMessage("mismatched input ':=' expecting ';'");
        parse("class C { method m() { this.m() := 42; } }");
    }

    @Test
    public void expressionAsStatement() throws Exception {
        thrown.expect(DafnyParserException.class);
        thrown.expectMessage("mismatched input '+' expecting LPAREN");
        parse("class C { var f:int; } method m(c:C) { c.f+1; } }");
    }

    @Test
    public void doubleDecreases() throws Exception {
        thrown.expect(DafnyParserException.class);
        thrown.expectMessage("mismatched input 'decreases' expecting BLOCK_BEGIN");
        parse("method m() decreases 0 decreases 0 {}");
    }

    @Test
    public void doubleModifies() throws Exception {
        thrown.expect(DafnyParserException.class);
        thrown.expectMessage("mismatched input 'modifies' expecting BLOCK_BEGIN");
        parse("method m() modifies x modifies x {}");
    }

    private void parse(String program) throws Exception {
        TestUtil.mockProject(program);
    }

}