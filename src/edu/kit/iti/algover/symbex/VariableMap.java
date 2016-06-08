/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2016 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.symbex;

import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.Set;

import org.antlr.runtime.CommonToken;

import edu.kit.iti.algover.parser.DafnyParser;
import edu.kit.iti.algover.parser.DafnyTree;
import edu.kit.iti.algover.util.ImmutableList;
import edu.kit.iti.algover.util.Pair;

public class VariableMap implements Iterable<Pair<String, DafnyTree>> {

    public static final VariableMap EMPTY = new VariableMap();

    private final VariableMap parent;
    private final String var;
    private final DafnyTree value;

    public VariableMap assign(String var, DafnyTree value) {
        return new VariableMap(this, var, value);
    }

    private VariableMap(VariableMap variableMap, String var, DafnyTree value) {
        this.parent = variableMap;
        this.var = var.intern();
        this.value = value;
    }

    private VariableMap() {
        this.var = "PSEUDO_VALUE";
        this.value = null;
        this.parent = null;
    }

    public VariableMap anonymise(String v) {
        VariableMap vm = this;
        int count = 0;
        v = v.intern();
        while(vm != EMPTY) {
            if(vm.var == v && vm.value.toString().contains("#")) {
                count ++;
            }
            vm = vm.parent;
        }

        String anonName = v + "#" + (count+1);
        return assign(v, new DafnyTree(new CommonToken(DafnyParser.ID, anonName)));
    }

    public Set<String> findAnonymisingConsts() {
        Set<String> result = new HashSet<String>();
        VariableMap vm = this;
        while(vm != EMPTY) {
            if(vm.value.toString().contains("#")) {
                result.add(vm.value.getText());
            }
            vm = vm.parent;
        }
        return result;
    }

    @Deprecated
    public DafnyTree instantiate(DafnyTree expression) {
        DafnyTree result = instantiate0(expression, ImmutableList.<String>nil());
        if(result == null) {
            return expression;
        } else {
            return result;
        }
    }

    @Deprecated
    private DafnyTree instantiate0(DafnyTree expression, ImmutableList<String> exceptions) {

        int type = expression.getType();
        //no replacement for labels
        if(type == DafnyParser.LABEL){
            return expression;

        }
        if(type == DafnyParser.ID) {
            String name = expression.toString();
            if(exceptions.contains(name)) {
                // it is an exception: no replacement for bound variables.
                return expression;
            } else {
                DafnyTree replacement = get(name);
                return replacement;
            }
        }

        if(type == DafnyParser.ALL || type == DafnyParser.EX) {
            exceptions = exceptions.append(expression.getChild(0).getText());
        }

        DafnyTree result = null;
        for(int i = 0; i < expression.getChildCount(); i++) {
            DafnyTree kid = instantiate0(expression.getChild(i), exceptions);
            if(kid != null) {
                if(result == null) {
                    result = new DafnyTree(expression.token);
                    for (int j = 0; j < i; j++) {
                        result.addChild(expression.getChild(j));
                    }
                }
                result.addChild(kid);
            } else if(result != null) {
                result.addChild(expression.getChild(i));
            }
        }

        assert result == null || result.getChildCount() == expression.getChildCount();
        assert result == null || result.getType() == type;

        return result;
    }

    @Deprecated
    public DafnyTree get(String name) {

        if(this == EMPTY && !name.contains("#")) {
            return new DafnyTree(new CommonToken(DafnyParser.ID, name + "#pre"));
        }

        if(name.equals(var)) {
            if(parent != null) {
                return parent.instantiate(value);
            } else {
                return value;
            }
        } else {
            if(parent != null) {
                return parent.get(name);
            } else {
                return null;
            }
        }
    }

    public String toHistoryString() {
        StringBuilder sb = new StringBuilder();
        VariableMap vm = this;
        while(vm != EMPTY) {
            String nl = sb.length() == 0 ? "" : "\n";
            sb.insert(0, vm.var + ":=" + vm.value.toStringTree() + nl);
            vm = vm.parent;
        }
        return sb.toString();
    }

    @Deprecated
    public String toParallelAssignment() {
        StringBuilder sb = new StringBuilder();
        VariableMap vm = this;
        Set<String> done = new HashSet<String>();

        while(vm != EMPTY) {
            String sep = sb.length() > 0 ? " || " : "";
            if(!done.contains(vm.var)) {
                sb.append(sep + vm.var + ":=" + vm.get(vm.var).toStringTree());
                done.add(vm.var);
            }
            vm = vm.parent;
        }
        return sb.toString();
    }

    @Override
    public String toString() {
        return toHistoryString();
    }

    @Override
    public Iterator<Pair<String, DafnyTree>> iterator() {
        VariableMap vm = this;
        LinkedList<Pair<String, DafnyTree>> result = new LinkedList<>();
        while(vm != EMPTY) {
            result.addFirst(new Pair<>(var, value));
            vm = vm.parent;
        }
        return result.iterator();
    }

}
