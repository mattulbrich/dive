package edu.kit.iti.algover.script.interpreter;


import edu.kit.iti.algover.parser.DafnyException;
import edu.kit.iti.algover.parser.DafnyParserException;
import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.rules.TermParameter;
import edu.kit.iti.algover.script.ast.*;
import edu.kit.iti.algover.script.data.Value;
import edu.kit.iti.algover.script.data.VariableAssignment;
import edu.kit.iti.algover.script.parser.DefaultASTVisitor;
import edu.kit.iti.algover.script.parser.Visitor;
import edu.kit.iti.algover.term.Sequent;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.term.parser.TermParser;

import java.math.BigInteger;
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
    private final ProofNode goal;
    private MatcherApi<T> matcher;
    private List<Visitor> entryListeners = new ArrayList<>(),
            exitListeners = new ArrayList<>();

    public Evaluator(VariableAssignment assignment, ProofNode node) {
        state = new VariableAssignment(assignment); // unmodifiable version of assignment
        goal = node;
    }

    /**
     * Evaluation of an expression.
     *
     * @param truth
     * @return the value of the evaluated expression
     */
    public Value<T> eval(Expression truth) {
        return (Value) truth.accept(this);
    }

    @Override
    public Value<T> visit(BinaryExpression e) {
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
    public Value<Boolean> visit(MatchExpression match) throws IllegalStateException{
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
     * Visit a termliteral and evaluate it to the term object by using the termparser. The symboltable for parsing is taken form the goal node
     * @param term
     * @return A value of type term
     *
     */
    @Override
    public Value<TermParameter> visit(TermLiteral term){
        Value<TermParameter> termV = null;
        try {
            TermParser tp = new TermParser(goal.getPVC().getSymbolTable());
            tp.setSchemaMode(true);
            termV = new Value<>(Type.TERM, new TermParameter(tp.parse(term.getText()), goal.getSequent()));
        } catch (DafnyException | DafnyParserException e) {
            System.out.println("Could not translate term " + term.getText());
            throw new RuntimeException(e);
        }
        // return Value.from(term);

        return termV;
    }

    /**
     * Visit a Sequentliteral and evaluate it using the termparser.
     * @param sequentLiteral
     * @return a value object wrapping a sequent
     */
    @Override
    public Value<TermParameter> visit(SequentLiteral sequentLiteral){
        Value<TermParameter> seqValue = null;
        try {
            TermParser tp = new TermParser(goal.getPVC().getSymbolTable());
            tp.setSchemaMode(true);
            seqValue = new Value<>(Type.TERM, new TermParameter(tp.parseSequent(sequentLiteral.getText()), goal.getSequent()));

        } catch (DafnyException | DafnyParserException e) {
            System.out.println("Could not translate term " + sequentLiteral.getText());
           throw new RuntimeException(e);
        }
        return seqValue;

    }

    @Override
    public Value<String> visit(StringLiteral string) {
        return Value.from(string);
    }

    @Override
    public Value<T> visit(Variable variable){
        //get variable value
        Value<T> v = state.getValue(variable);
        if (v != null) {
            return v;
        } else {
            throw new RuntimeException("Variable " + variable + " was not initialized");
        }

    }

    @Override
    public Value<Boolean> visit(BooleanLiteral bool) {
        return bool.isValue() ? Value.TRUE : Value.FALSE;
    }


    @Override
    public Value<BigInteger> visit(IntegerLiteral integer) {
        return Value.from(integer);
    }

    @Override
    public Value<T> visit(UnaryExpression e) {
        Operator op = e.getOperator();
        Expression expr = e.getExpression();
        Value<T> exValue = (Value) expr.accept(this);
        return op.evaluate(exValue);
    }


    public VariableAssignment getState() {
        return this.state;
    }

    public ProofNode getGoal() {
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
