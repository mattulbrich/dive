/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
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

    private final Type type;

    private static final Pattern EXTRACHAR_PATTERN =
            Pattern.compile("[^-A-Za-z0-9+/*=%?!.$_~&^<>@]");

    private final String name;

    public SExpr(String name) {
        this(name, Type.NONE);
    }

    private List<SExpr> children;

    public SExpr(String name, Type type) {
        this.name = name;
        this.type = type;
        this.children = Collections.emptyList();
    }

    public SExpr(String name, List<SExpr> children) {
        this(name, Type.NONE, children);
    }

    public SExpr(String name, Type type, List<SExpr> children) {
        this.name = name;
        this.children = children;
        this.type = type;
    }

    public SExpr(String name, String... children) {
        this(name, Type.NONE, children);
    }

    public SExpr(String name, Type type, String[] children) {
        this.name = name;
        this.type = type;
        this.children = new ArrayList<SExpr>(children.length);
        for (String string : children) {
            this.children.add(new SExpr(string));
        }
    }

    public SExpr(String name, SExpr... children) {
        this(name, Type.NONE, children);
    }

    public SExpr(String name, Type type, SExpr... children) {
        this(name, type, Arrays.asList(children));
    }

    public SExpr(SExpr... children) {
        this("", children);
    }

    public SExpr(List<SExpr> children) {
        this("", children);
    }

    private void appendTo(StringBuilder sb) {
        boolean noSpace = name.isEmpty();
        String escapedName = getEscapedName();
        if (children.size() > 0) {
            sb.append("(").append(escapedName);
            for (SExpr child : children) {
                if (!noSpace) {
                    sb.append(" ");
                } else {
                    noSpace = false;
                }
                child.appendTo(sb);
            }
            sb.append(")");
        } else {
            if (escapedName.length() == 0) {
                sb.append("()");
            } else {
                sb.append(escapedName);
            }
        }
    }

    public String toString() {
        StringBuilder sb = new StringBuilder();
        appendTo(sb);
        return sb.toString();
    }

    public String getEscapedName() {
        if (EXTRACHAR_PATTERN.matcher(name).find()) {
            return "|" + name + "|";
        } else {
            return name;
        }
    }

    public Type getType() {
        return type;
    }

    public enum Type {INT, BOOL, UNIVERSE, NONE, HEAP}
}
