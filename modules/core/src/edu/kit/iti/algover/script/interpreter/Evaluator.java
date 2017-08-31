package edu.kit.iti.algover.script.interpreter;


import edu.kit.iti.algover.script.ast.*;
import edu.kit.iti.algover.script.data.GoalNode;
import edu.kit.iti.algover.script.data.Value;
import edu.kit.iti.algover.script.data.VariableAssignment;
import edu.kit.iti.algover.script.parser.DefaultASTVisitor;
import edu.kit.iti.algover.script.parser.Visitor;

import java.util.ArrayList;
import java.util.List;

/**
 * Class handling evaluation of expressions (visitor for expressions)
 *
 * @author S.Grebing
 * @author A. Weigl
 */
public class Evaluator<T> extends DefaultASTVisitor<Value> implements ScopeObservable {
    private final VariableAssignment state;
    private final GoalNode<T> goal;
    private MatcherApi<T> matcher;
    private List<Visitor> entryListeners = new ArrayList<>(),
            exitListeners = new ArrayList<>();

    public Evaluator(VariableAssignment assignment, GoalNode<T> node) {
        state = new VariableAssignment(assignment); // unmodifiable version of assignment
        goal = node;
    }

    /**
     * Evaluation of an expression.
     *
     * @param truth
     * @return
     */
    public Value eval(Expression truth) {
        return (Value) truth.accept(this);
    }

    @Override
    public Value visit(BinaryExpression e) {
        Value v1 = (Value) e.getLeft().accept(this);
        Value v2 = (Value) e.getRight().accept(this);
        Operator op = e.getOperator();
        return op.evaluate(v1, v2);
    }

    /**
     * Visit a match expression and evaluate expression using matcher
     *
     * @param match
     * @return
     */
    @Override
    public Value visit(MatchExpression match) {
        if (match.getSignature() != null && !match.getSignature().isEmpty()) {
            throw new IllegalStateException("not supported");
        }
        List<VariableAssignment> va = null;
        Value pattern = (Value) match.getPattern().accept(this);
        if (match.isDerivable()) {
        } else {
            if (pattern.getType() == Type.STRING) {
                va = matcher.matchLabel(goal, (String) pattern.getData());
            } else if (pattern.getType() == Type.TERM) {
                va = matcher.matchSeq(goal, (String) pattern.getData(), match.getSignature());
            }
        }


        return va != null && va.size() > 0 ? Value.TRUE : Value.FALSE;
    }

    /**
     * @param term
     * @return
     */
    @Override
    public Value visit(TermLiteral term) {
        return Value.from(term);
    }

    @Override
    public Value visit(StringLiteral string) {
        return Value.from(string);
    }

    @Override
    public Value visit(Variable variable) {
        //get variable value
        Value v = state.getValue(variable);
        if (v != null) {
            return v;
        } else {
            throw new RuntimeException("Variable " + variable + " was not initialized");
        }

    }

    @Override
    public Value visit(BooleanLiteral bool) {
        return bool.isValue() ? Value.TRUE : Value.FALSE;
    }


    @Override
    public Value visit(IntegerLiteral integer) {
        return Value.from(integer);
    }

    @Override
    public Value visit(UnaryExpression e) {
        Operator op = e.getOperator();
        Expression expr = e.getExpression();
        Value exValue = (Value) expr.accept(this);
        return op.evaluate(exValue);
    }


    public VariableAssignment getState() {
        return this.state;
    }

    public GoalNode<T> getGoal() {
        return this.goal;
    }

    public MatcherApi<T> getMatcher() {
        return this.matcher;
    }

    public void setMatcher(MatcherApi<T> matcher) {
        this.matcher = matcher;
    }

    public List<Visitor> getEntryListeners() {
        return this.entryListeners;
    }

    public List<Visitor> getExitListeners() {
        return this.exitListeners;
    }
}