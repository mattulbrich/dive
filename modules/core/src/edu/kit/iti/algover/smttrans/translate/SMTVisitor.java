package edu.kit.iti.algover.smttrans.translate;

import java.util.List;

import edu.kit.iti.algover.smttrans.translate.expressions.SMTExpression;
import edu.kit.iti.algover.term.ApplTerm;
import edu.kit.iti.algover.term.LetTerm;
import edu.kit.iti.algover.term.QuantTerm;
import edu.kit.iti.algover.term.TermVisitor;
import edu.kit.iti.algover.term.VariableTerm;

public class SMTVisitor implements TermVisitor<List<String>, SMTExpression, RuntimeException> {

    @Override
    public SMTExpression visit(VariableTerm variableTerm, List<String> arg) throws RuntimeException {
    	return null;
    }

    @Override
    public SMTExpression visit(QuantTerm quantTerm, List<String> arg) throws RuntimeException {
    	return null;
    }

    @Override
    public SMTExpression visit(ApplTerm applTerm, List<String> arg) throws RuntimeException {
    		return null;

    }

    @Override
    public SMTExpression visit(LetTerm letTerm, List<String> arg) throws RuntimeException {

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
