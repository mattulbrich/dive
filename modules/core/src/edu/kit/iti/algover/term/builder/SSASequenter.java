/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.term.builder;

import edu.kit.iti.algover.data.SymbolTable;
import edu.kit.iti.algover.parser.DafnyException;
import edu.kit.iti.algover.parser.DafnyParser;
import edu.kit.iti.algover.parser.DafnyTree;
import edu.kit.iti.algover.proof.ProofFormula;
import edu.kit.iti.algover.rules.TermSelector;
import edu.kit.iti.algover.symbex.AssertionElement;
import edu.kit.iti.algover.symbex.PathConditionElement;
import edu.kit.iti.algover.symbex.SymbexPath;
import edu.kit.iti.algover.term.ApplTerm;
import edu.kit.iti.algover.term.FunctionSymbol;
import edu.kit.iti.algover.term.Sequent;
import edu.kit.iti.algover.term.Sort;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.util.ImmutableList;
import edu.kit.iti.algover.util.Pair;

import java.util.ArrayList;
import java.util.Collections;
import java.util.Iterator;
import java.util.List;
import java.util.Map;

/**
 * The Single Static Assignment Sequenter is an alternative to the other
 * sequenters based on the {@link UpdateSequenter}.
 *
 * <p> Where those have one formula per path condition or proof obligation with
 * a local assignment history (possibly
 * inlined, simplified or aggregated), this sequenter collects the assignments
 * as equalities on the sequent. Thus, the same variable x may occur under
 * different names x, x_1, x_2, etc.
 *
 * @author Mattias Ulbrich
 */
public class SSASequenter implements PVCSequenter {

    @Override
    public String getName() {
        return "ssa";
    }

    @Override
    public String getDescriptiveName() {
        return "Single static assignment - new variable per assignment";
    }

    @Override
    public Sequent translate(SymbexPath pathThroughProgram, SymbolTable symbolTable,
                             Map<TermSelector, DafnyTree> referenceMap) throws DafnyException {

        try {
            TreeTermTranslator ttt = new TreeTermTranslator(symbolTable);
            SSAInstantiationVisitor visitor = new SSAInstantiationVisitor(ttt.getReferenceMap());

            // JK: REVIEW maybe use set here?
            // MU: No. That would probably not have the right order.
            // Elements are guaranteed to be unique.
            List<ProofFormula> antecedent = new ArrayList<>();

            ImmutableList<Pair<FunctionSymbol, FunctionSymbol>> endMapping;
            endMapping = createMapping(pathThroughProgram.getAssignmentHistory(), symbolTable, antecedent, ttt, visitor);

            // from a bug.
            assert endMapping.size() == pathThroughProgram.getAssignmentHistory().size();


            for (PathConditionElement element : pathThroughProgram.getPathConditions()) {
                assert isPrefix(element.getAssignmentHistory(), pathThroughProgram.getAssignmentHistory());
                ImmutableList<Pair<FunctionSymbol, FunctionSymbol>> mapping =
                        endMapping.takeFirst(element.getAssignmentHistory().size());
                antecedent.add(createProofFormula(mapping, ttt, element.getExpression(),
                        SequenterUtil.getLabel(element), visitor));
            }

            antecedent = SequenterUtil.coalesceDuplicates(antecedent);

            assert pathThroughProgram.getProofObligations().size() == 1;
            AssertionElement assertion = pathThroughProgram.getProofObligations().getLast();
            ProofFormula succedent = createProofFormula(endMapping, ttt,
                    assertion.getExpression(), "Assertion", visitor);
            return new Sequent(antecedent, Collections.singletonList(succedent));

        }  catch(TermBuildException tbe) {
            throw new DafnyException(tbe.getLocation(), tbe);
        }
    }

    private boolean isPrefix(ImmutableList<DafnyTree> part, ImmutableList<DafnyTree> full) {
        if (full.size() < part.size()) {
            return false;
        }
        return full.takeFirst(part.size()).equals(part);
    }

    private ProofFormula createProofFormula(ImmutableList<Pair<FunctionSymbol, FunctionSymbol>> mapping,
                                            TreeTermTranslator ttt,
                                            DafnyTree expression, String label,
                                            SSAInstantiationVisitor visitor) throws DafnyException {
        try {
            Term condition = ttt.build(expression);
            Term replacedCondition = condition.accept(visitor, mapping);
            if(replacedCondition == null)
                replacedCondition = condition;
            return new ProofFormula(replacedCondition, label);
        } catch (TermBuildException ex) {
            throw new DafnyException(expression, ex);
        }
    }

    private ImmutableList<Pair<FunctionSymbol,FunctionSymbol>>
                createMapping(ImmutableList<DafnyTree> assignmentHistory,
                              SymbolTable symbolTable,
                              List<ProofFormula> antecedent,
                              TreeTermTranslator ttt,
                              SSAInstantiationVisitor visitor)
            throws TermBuildException {

        TreeAssignmentTranslator tat = new TreeAssignmentTranslator(ttt);

        ImmutableList<Pair<FunctionSymbol, Term>> assignments =
                tat.translateToLinear(assignmentHistory).reverse();
        ImmutableList<Pair<FunctionSymbol, FunctionSymbol>> mapping =
                ImmutableList.nil();

        TermBuilder tb = new TermBuilder(symbolTable);

        Iterator<DafnyTree> treeIt = assignmentHistory.iterator();
        for (Pair<FunctionSymbol, Term> assignment : assignments) {
            
            FunctionSymbol fsymb = assignment.getFst();
            ImmutableList<Pair<FunctionSymbol, FunctionSymbol>> oldMapping = mapping;

            FunctionSymbol fsymbNew = createNextFunctionSymbol(fsymb, symbolTable);
            symbolTable.addFunctionSymbol(fsymbNew);
            mapping = mapping.append(new Pair<>(fsymb, fsymbNew));

            DafnyTree assignedTree = treeIt.next().getChild(1);
            if (assignedTree.getType() == DafnyParser.WILDCARD) {
                // Do not make an assignment for an anonymised value
                continue;
            }
            
            Term rhs = assignment.getSnd();
            Term replaced = rhs.accept(visitor, oldMapping);
            if (replaced == null) {
                replaced = rhs;
            }

            antecedent.add(new ProofFormula(tb.eq(new ApplTerm(fsymbNew), replaced),
                    SequenterUtil.PATH_LABEL));
        }

        return mapping;
    }

    private void addOldHeap(SymbolTable symbolTable) {
        FunctionSymbol oldHeap = new FunctionSymbol("$oldheap", Sort.HEAP);
        symbolTable.addFunctionSymbol(oldHeap);
    }

    private FunctionSymbol createNextFunctionSymbol(FunctionSymbol fsymb, SymbolTable symbolTable) {
        assert fsymb.getArity() == 0;
        String name = fsymb.getName();
        int index = 1;
        while(symbolTable.getFunctionSymbol(name + "_" + index) != null) {
            index ++;
        }
        return new FunctionSymbol(name + "_" + index, fsymb.getResultSort());
    }
}

class SSAInstantiationVisitor extends ReplacementVisitor<ImmutableList<Pair<FunctionSymbol, FunctionSymbol>>> {

    private Map<Term, DafnyTree> refMap;

    public SSAInstantiationVisitor(Map<Term, DafnyTree> refMap) {
        this.refMap = refMap;
    }

    @Override
    public Term visit(ApplTerm applTerm, ImmutableList<Pair<FunctionSymbol, FunctionSymbol>> mapping) throws TermBuildException {
        FunctionSymbol funcSymbol = applTerm.getFunctionSymbol();
        Pair<FunctionSymbol, FunctionSymbol> replacement = mapping.findLast(pair -> pair.fst == funcSymbol);
        Term result;
        if(replacement != null) {
            assert replacement.snd.getArity() == 0;
            result = new ApplTerm(replacement.snd);
        } else {
            result = super.visit(applTerm, mapping);
        }

        if (result != null && refMap.containsKey(applTerm)) {
            refMap.put(result, refMap.get(applTerm));
        }

        return result;
    }
}
