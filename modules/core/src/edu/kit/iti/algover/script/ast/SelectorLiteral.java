/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 *
 */
package edu.kit.iti.algover.script.ast;

import edu.kit.iti.algover.script.exceptions.NotWelldefinedException;
import edu.kit.iti.algover.script.parser.Visitor;
import org.antlr.v4.runtime.ParserRuleContext;

/**
 * (produced as a copy of StringLiteral)
 *
 * @author Mattias Ulbrich
 * @version 1 (28.04.17)
 */
public class SelectorLiteral extends Literal {
    private final String text;

    protected ParserRuleContext ruleContext;

    public SelectorLiteral(String text) {
        this.text = text;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public <T> T accept(Visitor<T> visitor) {
        return visitor.visit(this);
    }

    @Override
    public boolean hasMatchExpression() {
        return false;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public SelectorLiteral copy() {
        return new SelectorLiteral(text);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Type getType(Signature signature) throws NotWelldefinedException {
        return Type.SELECTOR;
    }

    public String getText() {
        return this.text;
    }

    public boolean equals(Object o) {
        if (o == this) return true;
        if (!(o instanceof SelectorLiteral)) return false;
        final SelectorLiteral other = (SelectorLiteral) o;
        if (!other.canEqual((Object) this)) return false;
        final Object this$text = this.getText();
        final Object other$text = other.getText();
        if (this$text == null ? other$text != null : !this$text.equals(other$text)) return false;
        return true;
    }

    public int hashCode() {
        final int PRIME = 59;
        int result = 1;
        final Object $text = this.getText();
        result = result * PRIME + ($text == null ? 43 : $text.hashCode());
        return result;
    }

    protected boolean canEqual(Object other) {
        return other instanceof SelectorLiteral;
    }

    public String toString() {
        return "SelectorLiteral(text=" + this.getText() + ")";
    }

    @Override
    public ParserRuleContext getRuleContext() {
        return this.ruleContext;
    }

    @Override
    public void setRuleContext(ParserRuleContext c) {
        this.ruleContext = c;
    }
}
