package edu.kit.iti.algover.util;

import java.util.Collection;

public final class StringValidators {

    private StringValidators() {
        throw new Error();
    }

    private static final String VALIDATOR_KIND = "validator";

    public static StringValidator minValidator(int min) {
        return string -> {
            try {
                int val = Integer.parseInt(string);
                if(val < min) {
                    throw new FormatException(VALIDATOR_KIND, "integer >= " + min + " expected", string);
                }
            } catch(NumberFormatException nfe) {
                throw new FormatException(VALIDATOR_KIND, "decimal integer expected", string);
            }
        };
    }

    public static StringValidator rangeValidator(int min, int max) {
        return string -> {
            try {
                int val = Integer.parseInt(string);
                if(val < min) {
                    throw new FormatException(VALIDATOR_KIND, "integer n with " + min + " <= " + val
                            + " <= " + max + " expected", string);
                }
            } catch(NumberFormatException nfe) {
                throw new FormatException(VALIDATOR_KIND, "decimal integer expected", string);
            }
        };
    }


    public static final StringValidator INTEGER_VALIDATOR =
            string -> {
                try {
                    Integer.parseInt(string);
                } catch(NumberFormatException nfe) {
                    throw new FormatException(VALIDATOR_KIND, "decimal integer expected", string);
                }
            };

    public static final StringValidator NON_NEGATIVE_VALIDATOR = minValidator(0);

    public static final StringValidator POSITIVE_VALIDATOR = minValidator(1);

    public static final StringValidator BOOLEAN_VALIDATOR =
            string -> {
                try {
                    Boolean.valueOf(string);
                } catch (NumberFormatException nfe) {
                    throw new FormatException(VALIDATOR_KIND, "Boolean expected", string);
                }
            };

    public static final StringValidator ANY_VALIDATOR = string -> {};

    public static final StringValidator oneOfValidator(Collection<? extends CharSequence> coll) {
        return string -> {
             if(!coll.contains(string)) {
                 throw new FormatException(VALIDATOR_KIND, "expected one of " + coll, string);
             }
        };
    }

}
