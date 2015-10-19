/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015 Karlsruhe Institute of Technology
 */

package edu.kit.iti.algover.smt;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;
import java.util.regex.Pattern;

/**
 * This class models s-expressions to be used for the SMT translation.
 *
 * Every s-expression has got a {@link #name} and a (potentially empty) list of
 * {@link #children}.
 *
 * They can be printed out, non-simple names are escaped for SMT.
 *
 * @author Mattias Ulbrich
 *
 */
public class SExpr {

    private static final Pattern EXTRACHAR_PATTERN =
            Pattern.compile("[^-A-Za-z0-9+/*=%?!.$_~&^<>@]");

    private final String name;

    private List<SExpr> children;

    public SExpr(String name) {
        this.name = name;
        this.children = Collections.emptyList();
    }

    public SExpr(String name, List<SExpr> children) {
        this.name = name;
        this.children = children;
    }

    public SExpr(String name, String... children) {
        this.name = name;
        this.children = new ArrayList<SExpr>();
        for (String string : children) {
            this.children.add(new SExpr(string));
        }
    }

    public SExpr(String name, SExpr... children) {
        this(name, Arrays.asList(children));
    }

    public SExpr(SExpr... children) {
        this("", children);
    }

    public SExpr(List<SExpr> children) {
        this("", children);
    }

    public String toString() {
        StringBuilder sb = new StringBuilder();
        appendTo(sb);
        return sb.toString();
    }

    public String getEscapedName() {
        if(EXTRACHAR_PATTERN.matcher(name).find()) {
            return "|" + name + "|";
        } else {
            return name;
        }
    }

    private void appendTo(StringBuilder sb) {
        if(children.size() > 0) {
            sb.append("(").append(getEscapedName());
            for (SExpr child : children) {
                sb.append(" ");
                child.appendTo(sb);
            }
            sb.append(")");
        } else {
            sb.append(getEscapedName());
        }
    }
}
