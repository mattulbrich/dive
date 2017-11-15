package edu.kit.iti.algover.script.ast;

import edu.kit.iti.algover.script.exceptions.NotWelldefinedException;
import edu.kit.iti.algover.script.parser.Visitor;

public class SequentLiteral extends Literal {

    private final String text;


    public SequentLiteral(String text) {
        if (text.charAt(0) == '\'')
            text = text.substring(1);
        if (text.charAt(text.length() - 1) == '\'') //remove last symbol
            text = text.substring(0, text.length() - 1);
        if (text.charAt(0) == '`')
            text = text.substring(0, text.length() - 2);
        this.text = text;
    }


    @Override
    public boolean hasMatchExpression() {
        return false;
    }

    @Override
    public Expression copy() {
        return new SequentLiteral(text);
    }

    @Override
    public Type getType(Signature signature) throws NotWelldefinedException {
        return Type.TERM;
    }

    @Override
    public <T> T accept(Visitor<T> visitor) {
        return visitor.visit(this);

    }

    public int hashCode() {
        final int PRIME = 59;
        int result = 1;
        final Object $text = this.getText();
        result = result * PRIME + ($text == null ? 43 : $text.hashCode());
        return result;
    }

    public boolean equals(Object o) {
        if (o == this) return true;
        if (!(o instanceof SequentLiteral)) return false;
        final SequentLiteral other = (SequentLiteral) o;
        if (!other.canEqual((Object) this)) return false;
        final Object this$text = this.getText();
        final Object other$text = other.getText();
        if (this$text == null ? other$text != null : !this$text.equals(other$text)) return false;
        return true;
    }

    protected boolean canEqual(Object other) {
        return other instanceof SequentLiteral;
    }

    public String getText() {
        return this.text;
    }
}
