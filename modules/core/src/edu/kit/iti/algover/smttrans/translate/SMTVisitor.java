package edu.kit.iti.algover.smttrans.translate;

import java.util.ArrayList;

import java.util.List;

import edu.kit.iti.algover.smttrans.translate.expressions.SMTApplExpression;
import edu.kit.iti.algover.smttrans.translate.expressions.SMTBVExpression;
import edu.kit.iti.algover.smttrans.translate.expressions.SMTConstExpression;
import edu.kit.iti.algover.smttrans.translate.expressions.SMTExpression;
import edu.kit.iti.algover.smttrans.translate.expressions.SMTLetExpression;
import edu.kit.iti.algover.smttrans.translate.expressions.SMTQuantExpression;
import edu.kit.iti.algover.smttrans.translate.expressions.SMTVarExpression;
import edu.kit.iti.algover.term.ApplTerm;
import edu.kit.iti.algover.term.FunctionSymbol;
import edu.kit.iti.algover.term.LetTerm;
import edu.kit.iti.algover.term.QuantTerm;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.term.TermVisitor;
import edu.kit.iti.algover.term.VariableTerm;
import edu.kit.iti.algover.util.Pair;
import edu.kit.iti.algover.util.Util;

public class SMTVisitor implements TermVisitor<Void, SMTExpression, RuntimeException> {

    @Override
    public SMTExpression visit(VariableTerm variableTerm, Void t) throws RuntimeException {
        String name = variableTerm.getName();
        return new SMTConstExpression(FSFactory.makeFS(name, variableTerm.getSort()));
    }

    @Override
    public SMTExpression visit(QuantTerm quantTerm, Void t) throws RuntimeException {

        VariableTerm boundVar = quantTerm.getBoundVar();

        SMTExpression formula = quantTerm.getTerm(0).accept(this, t);

        SMTBVExpression var = new SMTBVExpression(FSFactory.makeFS(boundVar.getName(), boundVar.getSort()));

        return new SMTQuantExpression(quantTerm.getQuantifier(), var, formula);

    }

    @Override
    public SMTExpression visit(ApplTerm applTerm, Void t) throws RuntimeException {
        FunctionSymbol fs = FSFactory.makeFS(applTerm.getFunctionSymbol());

        List<SMTExpression> children = Util.map(applTerm.getSubterms(), x -> x.accept(SMTVisitor.this, null));

        if (applTerm.countTerms() == 0) { // const

            SMTConstExpression sc = new SMTConstExpression(fs);

            return sc;
        }

        SMTApplExpression sa = new SMTApplExpression(fs, children);

        return sa;

    }

    @Override
    public SMTExpression visit(LetTerm letTerm, Void t) throws RuntimeException {
       

        SMTExpression inner = letTerm.getTerm(0).accept(this, null);
        List<SMTExpression> subs = new ArrayList<>();

        for (Pair<VariableTerm, Term> pair : letTerm.getSubstitutions()) {

            subs.add(new SMTVarExpression(FSFactory.makeFS(pair.fst.getName(), pair.fst.getSort()),
                    pair.snd.accept(this, null)));

        }
        return new SMTLetExpression(subs, inner);
    }

}
