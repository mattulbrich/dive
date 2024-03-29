/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.parser;

import edu.kit.iti.algover.KnownRegression;
import edu.kit.iti.algover.util.TestUtil;
import org.antlr.runtime.MismatchedSetException;
import org.hamcrest.BaseMatcher;
import org.hamcrest.Description;
import org.hamcrest.Matcher;
import org.junit.Ignore;
import org.junit.Rule;
import org.junit.Test;
import org.junit.experimental.categories.Category;
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
        thrown.expectMessage("element selection requires a sequence, array, multiset (got int)");
        parse("method m(i:int) { i[0] := 0; }");
    }

    @Test
    public void wrongMultiDimension1() throws Exception {
        thrown.expect(DafnyException.class);
        thrown.expectMessage("Assigning a value of type int to an entitity of type $tuple<int,int>");
        parse("method m() returns (a:int) { } " +
                "method test() { var x,y:int; x,y := m(); }");
    }

    @Test
    public void wrongMultiDimension2() throws Exception {
        thrown.expect(DafnyException.class);
        thrown.expectMessage("Assigning a value of type $tuple<int,int> to an entitity of type int");
        parse("method m() returns (a:int, b:int) { } " +
                "method test() { var x,y:int; x := m(); }");
    }

    @Test
    public void wrongNumberOfArgs() throws Exception {
        thrown.expect(DafnyException.class);
        thrown.expectMessage("Wrong number of arguments in call to m. Expected 1, but received 2");
        parse("method m(x : int) { } " +
                "method test() { m(1,2); }");
    }

    // correctness feature request.
    @Test
    public void parametersMustNotBeModified() throws Exception {
        thrown.expect(DafnyException.class);
        thrown.expectMessage("");
        parse("method m(i:int) { i := 2; }");
    }

    // correctness feature request.
    @Test
    public void parametersMustNotBeModified2() throws Exception {
        thrown.expect(DafnyException.class);
        thrown.expectMessage("Assignment to method parameter s not allowed");
        parse("method m(a:array<int>, s:seq<int>) { a[0] := 0; s[0] := 0;}");
    }

    @Test
    public void parametersMustNotBeModifiedMulti() throws Exception {
        thrown.expect(DafnyException.class);
        thrown.expectMessage("Assignment to method parameter p not allowed");
        parse("method f() returns (a:int, b:int) { } " +
                "method m(p: int) { var q:int; q, p := f(); }");
    }

    @Test
    public void recursiveVariableDeclaration() throws Exception {
        thrown.expect(DafnyException.class);
        thrown.expectMessage("Unknown identifier: y");
        parse("method m() { var y:=y; }");
    }


    // After grammar change
    @Test
    public void wrongTypeVarDecl() throws Exception {
        thrown.expect(DafnyException.class);
        thrown.expectMessage("Assigning a value of type int to an entitity of type bool");
        parse("method m() { var b : bool := 42; }");
    }

    @Test
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

    // used to go through
    @Test
    public void methodInExpression() throws Exception {
        thrown.expect(DafnyException.class);
        thrown.expectMessage("Method calls must not be used in expressions");
        parse("method m() returns (r:int) { var x := m() + m(); }");
    }

    // used to produce a NPE
    @Test
    public void assigningAVoidMethodInVar() throws Exception {
        thrown.expect(DafnyException.class);
        thrown.expectMessage("Using the result of a method without return value");
        parse("method m() { var x := m(); }");
    }

    // used to produce a NPE
    @Test
    public void assigningAVoidMethod() throws Exception {
        thrown.expect(DafnyException.class);
        thrown.expectMessage("Using the result of a method without return value");
        parse("method m() { var x: int; x := m(); }");
    }

    private void parse(String program) throws Exception {
        TestUtil.mockProject(program);
    }


    @Test
    public void doubleDecl1() throws Exception {
        thrown.expect(DafnyException.class);
        thrown.expectMessage("Variable r already defined in this scope");
        parse("method m() returns (r: int) { var r: int; r:=5; }");
    }

    @Test
    public void doubleDecl2() throws Exception {
        thrown.expect(DafnyException.class);
        thrown.expectMessage("Variable r already defined in this scope");
        parse("method m() returns (r: int) { var r: int; var r: int; r:=5; }");
    }

    @Test
    public void doubleDecl3() throws Exception {
        thrown.expect(DafnyException.class);
        thrown.expectMessage("This scope already contains a declaration named m");
        parse("method m() { } method m() { }");
    }

    @Test
    public void doubleDecl4() throws Exception {
        thrown.expect(DafnyException.class);
        thrown.expectMessage("This scope already contains a declaration named m");
        parse("class C { method m() { } function m() : int { 0 } }");
    }

    // was an assertion error.
    @Test
    public void unknownClass() throws Exception {
        thrown.expect(DafnyException.class);
        thrown.expectMessage("Unknown identifier: node");
        parse("class C { method m() { node.next := node.next.next; } }");
    }

}