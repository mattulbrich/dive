package edu.kit.iti.algover.rules;

/**
 * Created by jklamroth on 2/1/18.
 */
public class DafnyRuleException extends Exception {
    public DafnyRuleException() {
        super();
    }

    public DafnyRuleException(String message) {
        super(message);
    }

    public DafnyRuleException(String message, Throwable cause) {
        super(message, cause);
    }
}
