package edu.kit.iti.algover;

import java.util.HashSet;
import java.util.Set;

import org.antlr.runtime.CommonToken;

import edu.kit.iti.algover.parser.PseudoParser;
import edu.kit.iti.algover.parser.PseudoTree;

public class VariableMap {

    public static final VariableMap EMPTY = new VariableMap();

    private VariableMap parent;
    private String var;
    private PseudoTree value;

    public VariableMap assign(String var, PseudoTree value) {
        return new VariableMap(this, var, value);
    }

    private VariableMap(VariableMap variableMap, String var, PseudoTree value) {
        this.parent = variableMap;
        this.var = var.intern();
        this.value = value;
    }

    private VariableMap() {
        this.var = "PSEUDO_VALUE";
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
        return assign(v, new PseudoTree(new CommonToken(PseudoParser.ID, anonName)));
    }

    public PseudoTree instantiate(PseudoTree expression) {
        PseudoTree result = instantiate0(expression);
        if(result == null) {
            return expression;
        } else {
            return result;
        }
    }

    private PseudoTree instantiate0(PseudoTree expression) {

        if(expression.getType() == PseudoParser.ID) {
            String name = expression.toString();
            PseudoTree replacement = get(name);
            return replacement;
        }

        PseudoTree result = null;
        for(int i = 0; i < expression.getChildCount(); i++) {
            PseudoTree kid = instantiate0(expression.getChild(i));
            if(kid != null) {
                if(result == null) {
                    result = new PseudoTree(expression.token);
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
        assert result == null || result.getType() == expression.getType();

        return result;
    }

    private PseudoTree get(String name) {

        if(this == EMPTY && !name.contains("#")) {
            return new PseudoTree(new CommonToken(PseudoParser.ID, name + "#pre"));
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

}
