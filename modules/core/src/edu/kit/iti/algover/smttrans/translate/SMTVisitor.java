package edu.kit.iti.algover.smttrans.translate;

import java.util.ArrayList;
import java.util.List;

import edu.kit.iti.algover.smttrans.data.Operation;
import edu.kit.iti.algover.smttrans.translate.expressions.SMTApplExpression;
import edu.kit.iti.algover.smttrans.translate.expressions.SMTConstExpression;
import edu.kit.iti.algover.smttrans.translate.expressions.SMTExpression;
import edu.kit.iti.algover.smttrans.translate.expressions.SMTLetExpression;
import edu.kit.iti.algover.smttrans.translate.expressions.SMTQuantExpression;
import edu.kit.iti.algover.smttrans.translate.expressions.SMTVarExpression;
import edu.kit.iti.algover.term.ApplTerm;
import edu.kit.iti.algover.term.LetTerm;
import edu.kit.iti.algover.term.QuantTerm;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.term.TermVisitor;
import edu.kit.iti.algover.term.VariableTerm;
import edu.kit.iti.algover.util.Pair;
import edu.kit.iti.algover.util.Util;

public class SMTVisitor implements TermVisitor<Type, SMTExpression, RuntimeException> {

    @Override
    public SMTExpression visit(VariableTerm variableTerm, Type t) throws RuntimeException {
        //return new SMTVarExpression(variableTerm.getName(), variableTerm.getTerm(0).accept(this, t)); // ?
        return new SMTConstExpression(variableTerm.getName()); //TODO
    }

    @Override
    public SMTExpression visit(QuantTerm quantTerm, Type t) throws RuntimeException {

        Operation quantifier;
        switch (quantTerm.getQuantifier()) {
        case EXISTS:
            quantifier = Operation.EXISTS;
            break;
        case FORALL:
            quantifier = Operation.FORALL;
            break;
        default:
            throw new UnsupportedOperationException("Unknown quantifier"); 
        }
      //multiple bound vars ?
        VariableTerm boundVar = quantTerm.getBoundVar();
        // String varname = "var$" + boundVar.getName();
        
        //
        // SExpr qvar = new SExpr(varname, "Int");
        // SExpr qqvar = new SExpr(qvar);
        // SExpr formula = term.getTerm(0).accept(this, null);
        //
        // return new SExpr(quantifier, BOOL, qqvar, formula);
        
       SMTExpression formula = quantTerm.getTerm(0).accept(this, t);
        System.out.println("QUANT: " + quantTerm.toString());
        
        System.out.println("Q " + quantifier.name());
        System.out.println("BV: " + boundVar.toString() + " : " + boundVar.getSort().getName());
        //SMTExpression var = boundVar.accept(this, t);
        SMTVarExpression var = new SMTVarExpression(boundVar.getName(), new SMTConstExpression(boundVar.getSort().getName()));
        System.out.println("F " + quantTerm.getTerm(0).toString());
        return new SMTQuantExpression(quantifier, Type.makeBoolType(), var, formula);
       // return new SMTConstExpression("debug", Type.makeIntType());
    }

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

    @Override
    public SMTExpression visit(ApplTerm applTerm, Type t) throws RuntimeException {
        String fs = applTerm.getFunctionSymbol().getName();
        Type currentType = Type.typeOperation(applTerm.getFunctionSymbol().getName());
        List<SMTExpression> children = Util.map(applTerm.getSubterms(), x -> x.accept(SMTVisitor.this, currentType));

        if (applTerm.countTerms() == 0) { // const

            SMTConstExpression sc = new SMTConstExpression(fs, t);
            // System.out.println(sc.toPSMT());
            return sc;
        }
        // System.out.println(applTerm.toString());

        // System.out.println("T " + currentType.toString());
        // System.out.println("FS " + fs);

        // if (currentType.getArity() > 1) {
        // return new SMTApplExpression(Type.getFS(fs), currentType.pop(), children);
        // }
        // return new SMTApplExpression(Type.getFS(fs), Type.makeBoolType(), children);

        SMTApplExpression sa = new SMTApplExpression(Type.getFS(fs), currentType, children);

        // if (Iterables.size(operators) > 1) {
        // return new
        // SMTExpression(OperationMatcher.matchOp(Iterables.get(operators,0)),
        // ops.subList(1, ops.size()),children);
        // } else {
        // return new
        // SMTExpression(OperationMatcher.matchOp(Iterables.get(operators,0)),
        // children);
        // }

        return sa;

    }

    @Override
    public SMTExpression visit(LetTerm letTerm, Type t) throws RuntimeException {
        // System.out.println("LT " + letTerm.toString());
        SMTExpression inner = letTerm.getTerm(0).accept(this, t);
        List<SMTExpression> subs = new ArrayList<>();

        System.out.println("!");
        for (Pair<VariableTerm, Term> pair : letTerm.getSubstitutions()) {
            subs.add(new SMTVarExpression(pair.fst.getName(), pair.snd.accept(this, t)));
            System.out.println(pair.toString());
        }
        return new SMTLetExpression(subs, inner);
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
