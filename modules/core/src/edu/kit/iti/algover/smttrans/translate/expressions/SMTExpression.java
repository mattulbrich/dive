package edu.kit.iti.algover.smttrans.translate.expressions;

import java.util.ArrayList;
import java.util.List;

import edu.kit.iti.algover.term.FunctionSymbol;

public abstract class SMTExpression {
    protected FunctionSymbol fs;
    protected List<SMTExpression> children = new ArrayList<>();

    public abstract String toSMT();

    public SMTExpression(FunctionSymbol f, List<SMTExpression> c) {
        this.fs = f;
        this.children = c;
    }

    public SMTExpression() {

    }

    public SMTExpression(FunctionSymbol f) {
        this.fs = f;
    }
}

// import java.util.ArrayList;
// import java.util.Collection;
// import java.util.LinkedHashSet;
// import java.util.List;
//
// import edu.kit.iti.algover.smttrans.data.Operation;
// import edu.kit.iti.algover.smttrans.data.OperationMatcher;
// import edu.kit.iti.algover.smttrans.translate.Dependency;
// import edu.kit.iti.algover.smttrans.translate.Type;
// import edu.kit.iti.algover.util.Pair;
//
// public abstract class SMTExpression {
//
// protected Operation op;
// protected Type type;
// protected List<SMTExpression> children;
//
// public abstract Pair<LinkedHashSet<Dependency>, String> toSMT();
//
// public SMTExpression(String op, Type type, List<SMTExpression> children) {
// this.op = OperationMatcher.matchOp(op);
// this.type = type;
// this.children = children;
// }
//
// public SMTExpression(Operation op, Type type, ArrayList<SMTExpression>
// children) {
// this.op = op;
// this.type = type;
// this.children = children;
// }
//
// public SMTExpression(String op, Type type) {
// this.op = OperationMatcher.matchOp(op);
// this.type = type;
// this.children = new ArrayList<>();
// }
//
// public SMTExpression(Operation op, Type type) {
// this.op = op;
// this.type = type;
// this.children = new ArrayList<>();
// }
// public SMTExpression(String op) {
// this.op = OperationMatcher.matchOp(op);
// this.type = new Type();
// this.children = new ArrayList<>();
// }
//
// public SMTExpression(Operation op) {
// this.op = op;
// this.type = new Type();
// this.children = new ArrayList<>();
// }
//
// public Type getType() {
// return type;
// }
//
// }
