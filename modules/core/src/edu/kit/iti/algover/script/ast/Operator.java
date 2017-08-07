package edu.kit.iti.algover.script.ast;

/*-
 * #%L
 * ProofScriptParser
 * %%
 * Copyright (C) 2017 Application-oriented Formal Verification
 * %%
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as
 * published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 * 
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 * 
 * You should have received a copy of the GNU General Public
 * License along with this program.  If not, see
 * <http://www.gnu.org/licenses/gpl-3.0.html>.
 * #L%
 */


import edu.kit.iti.algover.script.data.Value;

import java.math.BigInteger;
import java.util.function.BiFunction;
import java.util.function.UnaryOperator;


/**
 * An enum which contains meta-data to all operators.
 * <p>
 * <p>
 * Precedence: zero is preserved for literals!
 *
 * @author Alexander Weigl
 * @version 1 (28.04.17)
 */
public enum Operator {

    /**
     * special entry for marking match as an atomic expression.
     */
    MATCH("match", 1000, Type.BOOL) {
        @Override
        public Value evaluate(Value... v) {
            //return Value.from(v[0].getData().equals(v[1]));
            return null;
        }
    },
    /**
     *
     */
    NOT("not", "¬", 10, Type.BOOL, Type.BOOL) {
        @Override
        public Value evaluate(Value... v) {
            return Value.from(!(Boolean) v[0].getData());
        }
    },
    /** */
    NEGATE("-", "-", 10, Type.INT, Type.INT) {
        @Override
        public Value evaluate(Value... v) {
            return evaluate(BigInteger::negate, v);
        }
    },
    /** */
    MULTIPLY("*", "×", 20, Type.INT, Type.INT, Type.INT) {
        @Override
        public Value evaluate(Value... v) {
            return evaluate(BigInteger::multiply, v);
        }
    },
    /** */
    DIVISION("/", "÷", 20, Type.INT, Type.INT, Type.INT) {
        @Override
        public Value evaluate(Value... v) {
            return evaluate(BigInteger::divide, v);
        }
    },
    /** */
    PLUS("+", 30, Type.INT, Type.INT, Type.INT) {
        @Override
        public Value evaluate(Value... v) {
            return evaluate(BigInteger::add, v);
        }
    },
    /** */
    MINUS("-", 30, Type.INT, Type.INT, Type.INT) {
        @Override
        public Value evaluate(Value... v) {
            return evaluate(BigInteger::subtract, v);
        }
    },
    /** */
    LE("<", 40, Type.INT, Type.INT, Type.BOOL) {
        @Override
        public Value evaluate(Value... v) {
            return Value.from((((BigInteger) v[0].getData()).compareTo((BigInteger) v[1].getData()) < 0));
        }
    },
    /** */
    GE(">", 40, Type.INT, Type.INT, Type.BOOL) {
        @Override
        public Value evaluate(Value... v) {

            return Value.from((((BigInteger) v[0].getData()).compareTo((BigInteger) v[1].getData()) > 0));
        }
    },
    /** */
    LEQ("<=", "≤", 40, Type.INT, Type.INT, Type.BOOL) {
        @Override
        public Value evaluate(Value... v) {

            return Value.from((((BigInteger) v[0].getData()).compareTo((BigInteger) v[1].getData()) <= 0));
        }
    },
    /** */
    GEQ(">=", "≥", 40, Type.INT, Type.INT, Type.BOOL) {
        @Override
        public Value evaluate(Value... v) {
            return Value.from((((BigInteger) v[0].getData()).compareTo((BigInteger) v[1].getData()) >= 0));
        }
    },
    /** */
    EQ("=", "≡", 50, Type.INT, Type.INT, Type.BOOL) {
        @Override
        public Value evaluate(Value... v) {
            return Value.from((((BigInteger) v[0].getData()).compareTo((BigInteger) v[1].getData()) == 0));

        }
    },
    /** */
    NEQ("<>", "≢", 50, Type.INT, Type.INT, Type.BOOL) {
        @Override
        public Value evaluate(Value... v) {
            return Value.from((((BigInteger) v[0].getData()).compareTo((BigInteger) v[1].getData()) != 0));
        }
    },
    /** */
    AND("&", "∧", 60, Type.BOOL, Type.BOOL, Type.BOOL) {
        @Override
        public Value evaluate(Value... v) {

            return Value.from((Boolean) v[0].getData() & (Boolean) v[1].getData());
        }
    },
    /** */
    OR("|", "∨", 70, Type.BOOL, Type.BOOL, Type.BOOL) {
        @Override
        public Value evaluate(Value... v) {
            return Value.from((Boolean) v[0].getData() | (Boolean) v[1].getData());

        }
    },
    /** */
    IMPLICATION("==>", "⇒", 80, Type.BOOL, Type.BOOL, Type.BOOL) {
        @Override
        public Value evaluate(Value... v) {
            return Value.from(!(Boolean) v[0].getData() | (Boolean) v[1].getData());
        }
    },
    /**
     *
     * */
    EQUIVALENCE("<=>", "⇔", 90, Type.BOOL, Type.BOOL, Type.BOOL) {
        @Override
        public Value evaluate(Value... v) {
            return Value.from((!(Boolean) v[0].getData() | (Boolean) v[1].getData()) & ((Boolean) v[0].getData() | !(Boolean) v[1].getData()));
        }
    };


    private final String symbol;
    private final String unicode;
    private final int precedence;
    private final Type[] type;

    Operator(String symbol, int precedence, Type... type) {
        this(symbol, symbol, precedence, type);
    }

    Operator(String symbol, String unicode, int precedence, Type... type) {
        this.symbol = symbol;
        this.unicode = unicode;
        this.precedence = precedence;
        this.type = type;
    }


    public static Value<BigInteger> evaluate(
            BiFunction<BigInteger, BigInteger, BigInteger> func, Value<BigInteger>[] v) {
        return Value.from(func.apply(v[0].getData(), v[1].getData()));
    }

    public static Value<BigInteger> evaluate(UnaryOperator<BigInteger> func, Value<BigInteger>[] v) {
        return Value.from(func.apply(v[0].getData()));
    }


    /**
     * unicode symbol of this operator
     *
     * @return a non-null string
     */
    public String unicode() {
        return unicode;
    }

    /**
     * a ascii symbol of this operator.
     *
     * @return a non-null string
     */
    public String symbol() {
        return symbol;
    }

    /**
     * Returns the precedence (bind strength) of this operator.
     * <p>
     * A low precedence bind stronger, e.g. literals are 0.
     */
    public int precedence() {
        return precedence;
    }

    /**
     * Returns all types (arguments and returntype) of operator.
     *
     * @return an array with the last entry is the return type
     * of this operator and all previous entries are the types of arguments.
     * @see #returnType()
     */
    public Type[] type() {
        return type;
    }

    /**
     * Returns the return type of operator.
     */
    public Type returnType() {
        return type[type.length - 1];
    }

    /**
     * Number of arguments of this operator.
     */
    public int arity() {
        return type.length - 1;
    }

    /**
     * Evaluate the collection of values using the operator
     *
     * @param v
     * @return
     */
    public abstract Value evaluate(Value... v);

}
