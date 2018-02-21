/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.term.builder;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Map;

import edu.kit.iti.algover.SymbexStateToFormula;
import edu.kit.iti.algover.data.SymbolTable;
import edu.kit.iti.algover.parser.DafnyException;
import edu.kit.iti.algover.parser.DafnyParser;
import edu.kit.iti.algover.parser.DafnyTree;
import edu.kit.iti.algover.proof.ProofFormula;
import edu.kit.iti.algover.references.ReferenceTools;
import edu.kit.iti.algover.rules.TermSelector;
import edu.kit.iti.algover.symbex.AssertionElement;
import edu.kit.iti.algover.symbex.PathConditionElement;
import edu.kit.iti.algover.symbex.SymbexPath;
import edu.kit.iti.algover.term.FunctionSymbol;
import edu.kit.iti.algover.term.Sequent;
import edu.kit.iti.algover.term.Sort;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.util.ImmutableList;

/**
 * Update sequencer are a family of different sequent translation algorithms
 * that result in a let-cascade modelling the history assignments.
 *
 * For example, the program
 * <pre>
 *     a := 1; a := a + 1; assert a > 0;
 * </pre>
 * would generally be translated into
 * <pre>
 *     let a:=1 :: let a:=a+1 :: a > 0
 * </pre>
 *
 * The method {@link #postProcess(ProofFormula)} discerns the different members
 * of the family. They modify the original let-cascade according to their needs.
 *
 * @author Mattias Ulbrich
 */
public class UpdateSequenter implements PVCSequenter {

    @Override
    public String getName() {
        return "ass-seq";
    }

    @Override
    public String getDescriptiveName() {
        return "Sequence of assignments in front of every formula";
    }

    @Override
    public final Sequent translate(SymbexPath pathThroughProgram,
                                   SymbolTable makeSymbolTable,
                                   Map<TermSelector, DafnyTree> refMap)
                                           throws DafnyException {

        TreeTermTranslator ttt = new TreeTermTranslator(makeSymbolTable);
        List<ProofFormula> ante = new ArrayList<>();

        resolveWildcards(pathThroughProgram.getAssignmentHistory(),
                makeSymbolTable);

        for (PathConditionElement pce : pathThroughProgram.getPathConditions()) {
            try {
                Term term = ttt.build(pce.getAssignmentHistory(), pce.getExpression());
                ProofFormula formula = new ProofFormula(term);
                formula = postProcess(formula);
                ante.add(formula);
            } catch (TermBuildException e) {
                throw new DafnyException(pce.getExpression(), e);
            }
        }

        assert pathThroughProgram.getProofObligations().size() == 1;
        AssertionElement assertion = pathThroughProgram.getProofObligations().getHead();
        try {
            Term term = ttt.build(pathThroughProgram.getAssignmentHistory(),
                    assertion.getExpression());
            ProofFormula formula = new ProofFormula(term);
            formula = postProcess(formula);
            List<ProofFormula> succ = Collections.singletonList(formula);
            Sequent sequent = new Sequent(ante, succ);
            if(refMap != null) {
                ReferenceTools.addSequentReferences(sequent, ttt.getReferenceMap(), refMap);
            }
            return sequent;

        } catch (TermBuildException e) {
            throw new DafnyException(assertion.getExpression(), e);
        }

    }

    private void resolveWildcards(ImmutableList<DafnyTree> assignmentHistory, SymbolTable symbolTable) {
        for (DafnyTree ass : assignmentHistory) {
            DafnyTree value = ass.getChild(1);
            if (value.getType() != DafnyParser.WILDCARD) {
                continue;
            }

            DafnyTree receiver = ass.getChild(0);
            String suggestedName;
            if (receiver.getType() == DafnyParser.ID) {
                suggestedName = receiver.getText();
                // TODO : Field access, array access, ...
            } else {
                suggestedName = "unknown";
            }

            int count = 1;
            String name = suggestedName + "_" + count;
            while (symbolTable.getFunctionSymbol(name) != null) {
                count++;
                name = suggestedName + "_" + count;
            }
            Sort sort = SymbexStateToFormula.treeToType(receiver.getExpressionType());
            symbolTable.addFunctionSymbol(new FunctionSymbol(name, sort));

            value.removeAllChildren();
            value.addChild(new DafnyTree(DafnyParser.ID, name));
        }
    }

    /**
     * Modify the let-cascaded term that result from a translation.
     *
     * Originally, the method is the identity.
     *
     * @param formula The formula to rephrase.
     * @return A formula equivalent (yet syntactically different) to the
     * argument
     * @throws TermBuildException if the translation fails.
     */
    protected ProofFormula postProcess(ProofFormula formula) throws TermBuildException {
        return formula;
    }

}
