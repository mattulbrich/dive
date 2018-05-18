package edu.kit.iti.algover.util;

import de.uka.ilkd.pp.NoExceptions;
import edu.kit.iti.algover.rules.RuleException;
import edu.kit.iti.algover.rules.SubtermSelector;
import edu.kit.iti.algover.term.*;
import edu.kit.iti.algover.term.builder.TermBuildException;

import java.util.ArrayList;
import java.util.List;
import java.util.Optional;

// TODO Write tests for this
public class SubtermSelectorReplacementVisitor implements TermVisitor<SubtermSelector,Term,RuleException> {

    private final Term replacement;

    public SubtermSelectorReplacementVisitor(Term replacement) {
        this.replacement = replacement;
    }

    @Override
    public Term visit(VariableTerm variableTerm, SubtermSelector selector) throws RuleException {
        return checkReplacementAndSubselection(variableTerm, selector);
    }

    @Override
    public Term visit(SchemaVarTerm schemaVarTerm, SubtermSelector selector) throws RuleException {
        return checkReplacementAndSubselection(schemaVarTerm, selector);
    }

    @Override
    public Term visit(QuantTerm quantTerm, SubtermSelector selector) throws RuleException {
        Term simpleReplacement = checkReplacementAndSubselection(quantTerm, selector);
        if (simpleReplacement != null) {
            return simpleReplacement;
        }
        try {
            return new QuantTerm(
                        quantTerm.getQuantifier(),
                        quantTerm.getBoundVar(),
                        quantTerm.getTerm(0).accept(this, buildSubselector(selector)));
        } catch (TermBuildException e) {
            throw new RuleException(e);
        }
    }

    @Override
    public Term visit(ApplTerm applTerm, SubtermSelector selector) throws RuleException {
        Term simpleReplacement = checkReplacementAndSubselection(applTerm, selector);
        if (simpleReplacement != null) {
            return simpleReplacement;
        }

        List<Term> subterms = new ArrayList<>();

        for (int i = 0; i < applTerm.getSubterms().size(); i++) {
            if (i == selector.getPath().get(0)) {
                subterms.add(applTerm.getSubterms().get(i).accept(this, buildSubselector(selector)));
            } else {
                subterms.add(applTerm.getSubterms().get(i));
            }
        }

        try {
            return new ApplTerm(applTerm.getFunctionSymbol(),subterms);
        } catch (TermBuildException e) {
            throw new RuleException(e);
        }
    }

    @Override
    public Term visit(LetTerm letTerm, SubtermSelector selector) throws RuleException {
        Term simpleReplacement = checkReplacementAndSubselection(letTerm, selector);
        if (simpleReplacement != null) {
            return simpleReplacement;
        }


        try {
            if (selector.getPath().get(0) == 0) {
                return new LetTerm(letTerm.getSubstitutions(), letTerm.getTerm(0).accept(this, buildSubselector(selector)));
            }

            List<Pair<VariableTerm, Term>> substs = new ArrayList<>(letTerm.getSubstitutions().size());

            for (int i = 0; i < substs.size(); i++) {
                if (i == selector.getPath().get(0) - 1) {
                    substs.add(new Pair<>(
                            letTerm.getSubstitutions().get(i).getFst(),
                            letTerm.getSubstitutions().get(i).getSnd().accept(this, buildSubselector(selector))));
                } else {
                    substs.add(letTerm.getSubstitutions().get(i));
                }
            }

            return new LetTerm(substs, letTerm.getTerm(0));
        } catch (TermBuildException e) {
            throw new RuleException(e);
        }

    }

    private SubtermSelector buildSubselector(SubtermSelector selector) {
        int[] newPath = new int[selector.getPath().size() - 1];
        for (int i = 0; i < newPath.length; i++) {
            newPath[i] = selector.getPath().get(i + 1);
        }
        return new SubtermSelector(newPath);
    }

    private Term checkReplacementAndSubselection(Term term, SubtermSelector selector) throws RuleException {
        if (selector.getPath().isEmpty()) {
            return replacement;
        }

        if (term.getSubterms().size() == 0) {
            throw new RuleException("During replacing by subterm selector: SubtermSelector points outside the term (invalid depth).");
        }

        int immediatePath = selector.getPath().get(0);

        if (immediatePath >= term.getSubterms().size()) {
            throw new RuleException("During replacing by subterm selector: SubtermSelector points outside the term (invalid index).");
        }

        return null;
    }
}
