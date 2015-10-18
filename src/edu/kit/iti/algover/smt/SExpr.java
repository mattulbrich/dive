package edu.kit.iti.algover.smt;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;

public class SExpr {

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

    private void appendTo(StringBuilder sb) {
        if(children.size() > 0) {
            sb.append("(").append(name);
            for (SExpr child : children) {
                sb.append(" ");
                child.appendTo(sb);
            }
            sb.append(")");
        } else {
            sb.append(name);
        }
    }
}
