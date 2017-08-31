package edu.kit.iti.algover.script.data;

import edu.kit.iti.algover.script.ast.*;

import java.math.BigInteger;

/**
 * Class representing the values our variables may have
 *
 * @author S.Grebing
 * @author A. Weigl
 *         //TODO alle restlichen typen ergaenzen
 */
public class Value<T> {
    public static final Value TRUE = new Value<>(Type.BOOL, true);
    public static final Value FALSE = new Value<>(Type.BOOL, false);

    private final Type type;
    private final T data;

    @java.beans.ConstructorProperties({"type", "data"})
    public Value(Type type, T data) {
        this.type = type;
        this.data = data;
    }


    public static Value<BigInteger> from(IntegerLiteral i) {
        return new Value<>(Type.INT, i.getValue());
    }

    public static Value<BigInteger> from(Integer i) {
        return new Value<>(Type.INT, BigInteger.valueOf(i));
    }

    public static Value<String> from(StringLiteral s) {
        return new Value<>(Type.STRING, s.getText());
    }

    public static Value<Boolean> from(BooleanLiteral b) {
        return new Value(Type.BOOL, b.isValue());
    }

    public static Value<Boolean> from(boolean equals) {
        return new Value(Type.BOOL, equals);
    }

    public static Value<BigInteger> from(BigInteger apply) {
        return new Value<>(Type.INT, apply);
    }

    public static Value<String> from(String s) {
        return new Value<>(Type.STRING, s);
    }

    public static Value<String> from(TermLiteral term) {
        return new Value<>(Type.TERM, term.getText());
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        Value<?> value = (Value<?>) o;

        if (getType() != value.getType()) return false;
        return getData().equals(value.getData());
    }

    @Override
    public int hashCode() {
        int result = getType().hashCode();
        result = 31 * result + getData().hashCode();
        return result;
    }

    @Override
    public String toString() {
        return data + ":" + type;
    }

    public Type getType() {
        return this.type;
    }

    public T getData() {
        return this.data;
    }
}