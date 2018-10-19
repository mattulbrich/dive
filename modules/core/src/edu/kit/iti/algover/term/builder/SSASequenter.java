/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 *
 */

package edu.kit.iti.algover.term.builder;

import edu.kit.iti.algover.data.BuiltinSymbols;
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
import java.util.List;
import java.util.Map;

/**
 * The Single Static Assignment Sequenter is an alternative to the other sequenters based on the {@link
 * UpdateSequenter}.
 *
 * <p> Where those have one formula per path condition or proof obligation with a local assignment history (possibly
 * inlined, simplified or aggregated), this sequenter collects the assignments as equalities on the sequent. Thus,
 * the same variable x may occur under different names x, x_1, x_2, etc.
 *
 * @author Mattias Ulbrich
 */
public class SSASequenter implements PVCSequenter {

    private static final SSAInstantiationVisitor SSA_INSTANTIATION_VISITOR = new SSAInstantiationVisitor();

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

        //REVIEW maybe use set here?
        List<ProofFormula> antecedent = new ArrayList<>();

        ImmutableList<Pair<FunctionSymbol, FunctionSymbol>> endMapping;
        endMapping = createMapping(pathThroughProgram.getAssignmentHistory(), symbolTable, antecedent);

        // from a bug.
        assert endMapping.size() == pathThroughProgram.getAssignmentHistory().size();

        TreeTermTranslator ttt = new TreeTermTranslator(symbolTable);

        for (PathConditionElement element : pathThroughProgram.getPathConditions()) {
            System.out.println(element.getAssignmentHistory());
            System.out.println(pathThroughProgram.getAssignmentHistory());
            assert isPrefix(element.getAssignmentHistory(), pathThroughProgram.getAssignmentHistory());
            ImmutableList<Pair<FunctionSymbol, FunctionSymbol>> mapping =
                    endMapping.takeFirst(element.getAssignmentHistory().size());
            antecedent.add(createProofFormula(mapping, ttt, element.getExpression()));
        }

        assert pathThroughProgram.getProofObligations().size() == 1;
        AssertionElement assertion = pathThroughProgram.getProofObligations().getLast();
        ProofFormula succedent = createProofFormula(endMapping, ttt, assertion.getExpression());

        return new Sequent(antecedent, Collections.singletonList(succedent));
    }

    private boolean isPrefix(ImmutableList<DafnyTree> part, ImmutableList<DafnyTree> full) {
        if (full.size() < part.size()) {
            return false;
        }
        return full.takeFirst(part.size()).equals(part);
    }

    private ProofFormula createProofFormula(ImmutableList<Pair<FunctionSymbol, FunctionSymbol>> mapping,
                                            TreeTermTranslator ttt,
                                            DafnyTree expression) throws DafnyException {
        try {
            Term condition = ttt.build(expression);
            Term replacedCondition = condition.accept(SSA_INSTANTIATION_VISITOR, mapping);
            if(replacedCondition == null)
                replacedCondition = condition;
            return new ProofFormula(replacedCondition);
        } catch (TermBuildException ex) {
            throw new DafnyException(expression, ex);
        }
    }

    private ImmutableList<Pair<FunctionSymbol,FunctionSymbol>> createMapping(ImmutableList<DafnyTree> assignmentHistory,
                                                                             SymbolTable symbolTable,
                                                                             List<ProofFormula> antecedent) throws DafnyException {

        ImmutableList<Pair<FunctionSymbol,FunctionSymbol>> mapping = ImmutableList.nil();
        TreeTermTranslator ttt = new TreeTermTranslator(symbolTable);
        TermBuilder tb = new TermBuilder(symbolTable);
        addOldHeap(symbolTable);

        for (DafnyTree dafnyTree : assignmentHistory) {
            DafnyTree target = dafnyTree.getChild(0);
            DafnyTree assignedExpr = dafnyTree.getChild(1);

            try {
                FunctionSymbol fsymb;
                int targetType = target.getType();
                if(targetType == DafnyParser.ID) {
                    String lhs = dafnyTree.getChild(0).getText();
                    fsymb = symbolTable.getFunctionSymbol(lhs);
                } else {
                    assert targetType == DafnyParser.ARRAY_ACCESS || targetType == DafnyParser.FIELD_ACCESS;
                    fsymb = BuiltinSymbols.HEAP;
                }

                FunctionSymbol fsymbNew = createNextFunctionSymbol(fsymb, symbolTable);
                symbolTable.addFunctionSymbol(fsymbNew);

                ImmutableList<Pair<FunctionSymbol, FunctionSymbol>> oldMapping = mapping;

                mapping = mapping.append(new Pair<>(fsymb, fsymbNew));

                if (assignedExpr.getType() == DafnyParser.WILDCARD) {
                    // Do not add an assignment for an anonymised value
                    continue;
                }

                Term rhs = ttt.build(assignedExpr);

                if (targetType == DafnyParser.ARRAY_ACCESS) {
                    Term heap = new ApplTerm(BuiltinSymbols.HEAP);
                    Term arrayAccess = ttt.build(target);
                    rhs = tb.storeArray(heap, arrayAccess.getTerm(1), arrayAccess.getTerm(2), rhs);
                } else if (targetType == DafnyParser.FIELD_ACCESS) {
                    Term heap = new ApplTerm(BuiltinSymbols.HEAP);
                    Term fieldAccess = ttt.build(target);
                    rhs = tb.storeField(heap, fieldAccess.getTerm(1), fieldAccess.getTerm(2), rhs);
                }

                Term replaced = rhs.accept(SSA_INSTANTIATION_VISITOR, oldMapping);
                if (replaced == null) {
                    replaced = rhs;
                }

                antecedent.add(new ProofFormula(tb.eq(new ApplTerm(fsymbNew), replaced)));

            } catch(TermBuildException ex){
                throw new DafnyException(dafnyTree, ex);
            }
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

    @Override
    public Term visit(ApplTerm applTerm, ImmutableList<Pair<FunctionSymbol, FunctionSymbol>> mapping) throws TermBuildException {
        FunctionSymbol funcSymbol = applTerm.getFunctionSymbol();
        Pair<FunctionSymbol, FunctionSymbol> replacement = mapping.findLast(pair -> pair.fst == funcSymbol);
        if(replacement != null) {
            assert replacement.snd.getArity() == 0;
            return new ApplTerm(replacement.snd);
        } else {
            return super.visit(applTerm, mapping);
        }
    }
}
