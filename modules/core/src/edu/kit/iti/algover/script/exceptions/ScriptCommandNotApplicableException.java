package edu.kit.iti.algover.script.exceptions;


import edu.kit.iti.algover.rules.ProofRule;
import edu.kit.iti.algover.script.ast.CallStatement;

import java.util.Map;

/**
 * Exception for not applicable Rules
 */
public class ScriptCommandNotApplicableException extends RuntimeException {


    public ScriptCommandNotApplicableException(Exception e) {
        super(e);
    }

    public ScriptCommandNotApplicableException(ProofRule r, CallStatement call) {
        System.out.println("Rule " + r.getName() + " in line " + call.getStartPosition().getLineNumber() + " was not applicable");
    }


    public ScriptCommandNotApplicableException(Exception e, ProofRule r, CallStatement call) {
        System.out.println("Rule " + r.getName() + " in line " + call.getStartPosition().getLineNumber() + " was not applicable");
        e.printStackTrace();
    }

    public ScriptCommandNotApplicableException(Exception e, ProofRule c, Map<String, String> params) {
        StringBuffer sb = new StringBuffer();
        sb.append("Rule " + c.getName() + " with parameters ");
        for (String s : params.keySet()) {
            sb.append(params.get(s));
        }
        sb.append(" was not applicable");
        System.out.println(sb.toString());
        e.printStackTrace();
    }
}
