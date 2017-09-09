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

import edu.kit.iti.algover.data.SymbolTable;
import edu.kit.iti.algover.parser.DafnyException;
import edu.kit.iti.algover.parser.DafnyTree;
import edu.kit.iti.algover.proof.ProofFormula;
import edu.kit.iti.algover.references.ReferenceTools;
import edu.kit.iti.algover.rules.TermSelector;
import edu.kit.iti.algover.symbex.AssertionElement;
import edu.kit.iti.algover.symbex.PathConditionElement;
import edu.kit.iti.algover.symbex.SymbexPath;
import edu.kit.iti.algover.term.Sequent;
import edu.kit.iti.algover.term.Term;

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
        int id = 0;

        for (PathConditionElement pce : pathThroughProgram.getPathConditions()) {
            try {
                Term term = ttt.build(pce.getAssignmentHistory(), pce.getExpression());
                ProofFormula formula = new ProofFormula(id++, term);
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
            ProofFormula formula = new ProofFormula(id++, term);
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

    protected ProofFormula postProcess(ProofFormula formula) {
        return formula;
    }

}
