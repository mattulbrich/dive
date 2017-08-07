package edu.kit.iti.algover.script.exceptions;

import de.uka.ilkd.key.macros.scripts.RuleCommand;

import java.util.Map;

/**
 * Exception for not applicable Rules
 */
public class ScriptCommandNotApplicableException extends RuntimeException {

    public ScriptCommandNotApplicableException(Exception e) {
        super(e);
    }

    public ScriptCommandNotApplicableException(Exception e, RuleCommand c) {
        System.out.println("Call " + c.getName() + " was not applicable");
    }

    public ScriptCommandNotApplicableException(Exception e, RuleCommand c, Map<String, String> params) {
        StringBuffer sb = new StringBuffer();
        sb.append("Call " + c.getName() + " with parameters ");
        for (String s : params.keySet()) {
            sb.append(params.get(s));
        }
        sb.append(" was not applicable");
        System.out.println(sb.toString());
    }
}
