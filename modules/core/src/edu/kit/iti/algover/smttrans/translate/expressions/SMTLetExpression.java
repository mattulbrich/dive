package edu.kit.iti.algover.smttrans.translate.expressions;

import java.util.List;

public class SMTLetExpression extends SMTExpression {

    private SMTExpression inner;
    private List<SMTExpression> subs;

    public SMTLetExpression(List<SMTExpression> subs, SMTExpression inner) {
        super();
        this.subs = subs;
        this.inner = inner;
    }

    @Override
    public String toSMT(boolean... arg) {
        StringBuilder sb = new StringBuilder();
        sb.append("(let (");
        
        for (SMTExpression sub : subs) {
            sb.append("(");
            sb.append(sub.toSMT(false));
            sb.append(")");
        }
        sb.append(") ");
        if (inner instanceof SMTConstExpression) {
            sb.append(" (not ");
            sb.append(inner.toSMT(arg));
            sb.append("))");

        } else {

            sb.append(inner.toSMT(arg));
            sb.append("))");
        }
        sb.append(")");
        return sb.toString();
    }
    
    
//  StringBuilder sb = new StringBuilder();
//
//  sb.append(subs.get(0).toSMT(false));
//  sb.append(")" + "\r\n");
//
//  if (subs.size() > 1) {
//      for (SMTExpression s : subs.subList(1, subs.size())) {
//
//          sb.append("(assert " + s.toSMT(false) + ")" + "\r\n");
//      }
//
//  }
//
//  sb.append("(assert");
//  if (inner instanceof SMTConstExpression) {
//      sb.append(" (not ");
//      sb.append(inner.toSMT(arg));
//      sb.append("))");
//
//  } else {
//
//      sb.append(inner.toSMT(arg));
//      sb.append(")");
//  }
//
//  return sb.toString();


}
