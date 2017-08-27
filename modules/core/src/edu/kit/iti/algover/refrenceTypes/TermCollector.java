package edu.kit.iti.algover.refrenceTypes;

import de.uka.ilkd.pp.NoExceptions;
import edu.kit.iti.algover.rules.SubtermSelector;
import edu.kit.iti.algover.term.*;

import java.util.HashMap;
import java.util.Map;

/**
 * Created by Philipp on 27.08.2017.
 */
public class TermCollector implements TermVisitor<SubtermSelector, Void, NoExceptions> {

    private final Map<SubtermSelector, Term> collectedTerms;

    public TermCollector() {
        collectedTerms = new HashMap<>();
    }

    public Map<SubtermSelector, Term> getCollectedTerms() {
        return collectedTerms;
    }

    private Void visit(Term term, SubtermSelector selector) {
        collectedTerms.put(selector, term);
        for (int i = 0; i < term.countTerms(); i++) {
            SubtermSelector subSelector = new SubtermSelector(selector, i);
            term.getSubterms().get(i).accept(this, subSelector);
        }
        return null;
    }

    @Override
    public Void visit(VariableTerm variableTerm, SubtermSelector selector) throws NoExceptions {
        return visit(variableTerm, selector);
    }

    @Override
    public Void visit(SchemaVarTerm schemaVarTerm, SubtermSelector selector) throws NoExceptions {
        return visit(schemaVarTerm, selector);
    }

    @Override
    public Void visit(QuantTerm quantTerm, SubtermSelector selector) throws NoExceptions {
        return visit(quantTerm, selector);
    }

    @Override
    public Void visit(ApplTerm applTerm, SubtermSelector selector) throws NoExceptions {
        return visit(applTerm, selector);
    }

    @Override
    public Void visit(LetTerm letTerm, SubtermSelector selector) throws NoExceptions {
        return visit(letTerm, selector);
    }
}
