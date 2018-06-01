package edu.kit.iti.algover.smttrans.translate;

import java.util.Arrays;
import java.util.List;

import com.google.common.base.CharMatcher;
import com.google.common.base.Splitter;
import com.google.common.collect.Iterables;

import edu.kit.iti.algover.smttrans.translate.expressions.SMTExpression;
import edu.kit.iti.algover.term.ApplTerm;
import edu.kit.iti.algover.term.LetTerm;
import edu.kit.iti.algover.term.QuantTerm;
import edu.kit.iti.algover.term.TermVisitor;
import edu.kit.iti.algover.term.VariableTerm;
import edu.kit.iti.algover.util.Util;
import edu.kit.iti.algover.smttrans.data.OperationMatcher;

public class SMTVisitor implements TermVisitor<Type, SMTExpression, RuntimeException> {

    @Override
    public SMTExpression visit(VariableTerm variableTerm, Type t) throws RuntimeException {
        return null;
    }

    @Override
    public SMTExpression visit(QuantTerm quantTerm, Type t) throws RuntimeException {
        return null;
    }

    @Override
    public SMTExpression visit(ApplTerm applTerm, Type t) throws RuntimeException {
        Type currentType = Type.typeOperation(applTerm.getFunctionSymbol().getName());
        List<SMTExpression> children = Util.map(applTerm.getSubterms(), x -> x.accept(SMTVisitor.this, currentType));

        if (applTerm.countTerms() == 0) { // const
            
            System.out.println("CONST " + applTerm.toString() + " : " + t.toString());
            //System.out.println("CONST-FS: ");
             //return new SMTConstExpression(operator, arg, nul);
        }
       // if (Iterables.size(operators) > 1) {
            // return new SMTExpression(OperationMatcher.matchOp(Iterables.get(operators,
            // 0)), ops.subList(1, ops.size()),
            // children);
       // } else {
            // return new SMTExpression(OperationMatcher.matchOp(Iterables.get(operators,
            // 0)), children);
       // }
        
        return null;

    }

    @Override
    public SMTExpression visit(LetTerm letTerm, Type t) throws RuntimeException {

        return null;
    }

    // public SExpr visit(LetTerm letTerm, Void arg) {
    //
    // SExpr inner = letTerm.getTerm(0).accept(this, arg);
    // List<SExpr> substitutions = new ArrayList<SExpr>();
    // for (Pair<VariableTerm, Term> pair : letTerm.getSubstitutions()) {
    // substitutions.add(new SExpr("var$" + pair.fst.getName(),
    // pair.snd.accept(this, null)));
    // }
    // return new SExpr("let", UNIVERSE, new SExpr(substitutions), inner);

    // @Override
    // public SExpr visit(VariableTerm variableTerm, Void arg) {
    // return new SExpr("var$" + variableTerm.getName());
    // }
    //
    // @Override
    // public SExpr visit(QuantTerm term, Void arg) {
    // String quantifier;
    // switch (term.getQuantifier()) {
    // case EXISTS:
    // quantifier = "exists";
    // break;
    // case FORALL:
    // quantifier = "forall";
    // break;
    // default:
    // throw new UnsupportedOperationException("Unknown quantifier: " + term);
    // }
    //
    // VariableTerm boundVar = term.getBoundVar();
    // String varname = "var$" + boundVar.getName();
    //
    // SExpr qvar = new SExpr(varname, "Int");
    // SExpr qqvar = new SExpr(qvar);
    // SExpr formula = term.getTerm(0).accept(this, null);
    //
    // return new SExpr(quantifier, BOOL, qqvar, formula);
    // }
    //

    //
    // @Override
    // public SExpr visit(LetTerm letTerm, Void arg) {
    //
    // SExpr inner = letTerm.getTerm(0).accept(this, arg);
    // List<SExpr> substitutions = new ArrayList<SExpr>();
    // for (Pair<VariableTerm, Term> pair : letTerm.getSubstitutions()) {
    // substitutions.add(new SExpr("var$" + pair.fst.getName(),
    // pair.snd.accept(this, null)));
    // }
    // return new SExpr("let", UNIVERSE, new SExpr(substitutions), inner);
    // }

}
