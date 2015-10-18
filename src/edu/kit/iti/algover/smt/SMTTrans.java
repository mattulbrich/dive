package edu.kit.iti.algover.smt;

import java.io.IOException;
import java.io.InputStream;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Properties;

import edu.kit.iti.algover.term.ApplTerm;
import edu.kit.iti.algover.term.DefaultTermVisitor;
import edu.kit.iti.algover.term.FunctionSymbol;
import edu.kit.iti.algover.term.QuantTerm;
import edu.kit.iti.algover.term.SchemaVarTerm;
import edu.kit.iti.algover.term.Sort;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.term.VariableTerm;

public class SMTTrans extends DefaultTermVisitor<Void, SExpr> {

    private static Properties OP_MAP;
    static {
        OP_MAP = new Properties();
        try(InputStream fis = SMTTrans_Old.class.getResourceAsStream("opnames.txt")) {
            OP_MAP.load(fis);
        } catch (IOException e) {
            throw new Error(e);
        }
    }

    public SExpr trans(Term formula) {
        return formula.accept(this, null);
    }

    @Override
    protected SExpr defaultVisit(Term term, Void arg) {
        throw new Error("Missing method for " + term.getClass());
    }

    @Override
    public SExpr visit(ApplTerm term, Void arg) {

        FunctionSymbol f = term.getFunctionSymbol();
        String name = f.getName();
        if(OP_MAP.containsKey(name)) {
            name = OP_MAP.getProperty(name);
        }

        List<SExpr> children = new ArrayList<>();
        for (Term subterm : term.getSubterms()) {
            children.add(subterm.accept(this, null));
        }

        return new SExpr(name, children);
    }

    @Override
    public SExpr visit(QuantTerm term, Void arg) {

        String quantifier;
        switch (term.getQuantifier()) {
        case EXISTS:
            quantifier = "exists";
            break;
        case FORALL:
            quantifier = "forall";
            break;
        default:
            throw new UnsupportedOperationException("Unknown quantifier: " + term);
        }

        VariableTerm boundVar = term.getBoundVar();
        SExpr sort = typeToSMT(boundVar.getSort());
        SExpr qvar = new SExpr(boundVar.getName(), sort);
        SExpr qqvar = new SExpr(qvar);

        SExpr formula = term.getTerm(0).accept(this, null);

        return new SExpr(quantifier, qqvar, formula);
    }

    @Override
    public SExpr visit(SchemaVarTerm term, Void arg) {
        throw new UnsupportedOperationException("Schema variables are not supported for SMT solving");
    }

    @Override
    public SExpr visit(VariableTerm term, Void arg) {
        return new SExpr(term.getName());
    }

    // That is fine for now. ... Later redefinition is expected
    public static SExpr typeToSMT(Sort sort) {

        String name = sort.getName();
        if(name.matches("array[0-9]+")) {
            int dim = Integer.parseInt(name.substring(5));
            List<SExpr> args = Collections.nCopies(dim+1, new SExpr("Int"));
            return new SExpr("Array", args);
        } else {
            switch(name) {
            case "int": return new SExpr("Int");
            case "set": return new SExpr("Array", "Int", "Boolean");
            }
        }
        throw new UnsupportedOperationException("Unsupported sort: " + sort);
    }

}
