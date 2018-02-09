/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 *
 */

// Checkstyle: ALLOFF

package edu.kit.iti.algover.rules.impl;

import edu.kit.iti.algover.data.SymbolTable;
import edu.kit.iti.algover.proof.PVC;
import edu.kit.iti.algover.proof.ProofFormula;
import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.rules.AbstractProofRule;
import edu.kit.iti.algover.rules.Parameters;
import edu.kit.iti.algover.rules.ProofRuleApplication;
import edu.kit.iti.algover.rules.ProofRuleApplication.Applicability;
import edu.kit.iti.algover.rules.ProofRuleApplicationBuilder;
import edu.kit.iti.algover.rules.RuleException;
import edu.kit.iti.algover.rules.TermSelector;
import edu.kit.iti.algover.smt.SMTQuickNDirty;
import edu.kit.iti.algover.smt.SMTSolver.Result;
import edu.kit.iti.algover.smt.Z3Solver;
import edu.kit.iti.algover.term.FunctionSymbol;
import edu.kit.iti.algover.term.Sequent;
import edu.kit.iti.algover.term.Sort;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.term.builder.TermBuilder;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.OutputStream;
import java.util.ArrayList;
import java.util.List;

import static edu.kit.iti.algover.smt.SMTSolver.Result.SAT;


/*
 * This is a quick and dirty implementation until the real one is available
 */
public class Z3Rule extends AbstractProofRule {

    @Override
    public String getName() {
        return "z3";
    }

    @Override
    public ProofRuleApplication considerApplication(ProofNode target, Sequent selection, TermSelector selector) throws RuleException {
        ProofRuleApplicationBuilder builder = new ProofRuleApplicationBuilder(this);
        builder.setApplicability(Applicability.MAYBE_APPLICABLE);
        builder.setClosing();
        builder.setRefiner((app, param) -> refine(target, app));
        return builder.build();
    }

    private ProofRuleApplication refine(ProofNode target, ProofRuleApplication app) {
        PVC pvc = target.getPVC();

        if(quickAndDirty(target.getSequent(), pvc.getSymbolTable())) {
            ProofRuleApplicationBuilder builder = new ProofRuleApplicationBuilder(app);
            builder.setApplicability(Applicability.APPLICABLE);
            builder.setRefiner(null);
            return builder.build();
        } else {
            ProofRuleApplicationBuilder builder = new ProofRuleApplicationBuilder(app);
            builder.setApplicability(Applicability.NOT_APPLICABLE);
            builder.setRefiner(null);
            return builder.build();
        }

    }

    @Override
    public ProofRuleApplication makeApplication(ProofNode target, Parameters parameters) throws RuleException {
        PVC pvc = target.getPVC();

        if(quickAndDirty(target.getSequent(), pvc.getSymbolTable())) {
            ProofRuleApplicationBuilder builder = new ProofRuleApplicationBuilder(this);
            builder.setApplicability(Applicability.APPLICABLE);
            builder.setRefiner(null);
            return builder.build();
        } else {
            ProofRuleApplicationBuilder builder = new ProofRuleApplicationBuilder(this);
            builder.setApplicability(Applicability.NOT_APPLICABLE);
            builder.setRefiner(null);
            return builder.build();
        }
    }

    private boolean quickAndDirty(Sequent sequent, SymbolTable symbolTable) {

        StringBuilder sb = new StringBuilder();

        try {
            for (FunctionSymbol fs : symbolTable.getAllSymbols()) {
                if (fs.getResultSort().equals(Sort.INT) && fs.getArity() == 0) {
                    sb.append("(declare-const pv$" + fs.getName() + " Int)\n");
                }
                if (fs.getResultSort().equals(Sort.get("seq", Sort.INT)) && fs.getArity() == 0) {
                    sb.append("(declare-const pv$" + fs.getName() + " (Array Int Int))\n");
                }
            }
            for (ProofFormula proofFormula : sequent.getAntecedent()) {
                sb.append("(assert ")
                        .append(proofFormula.getTerm().accept(new SMTQuickNDirty(), null))
                        .append(")\n");
            }
            for (ProofFormula proofFormula : sequent.getSuccedent()) {
                sb.append("(assert (not ")
                        .append(proofFormula.getTerm().accept(new SMTQuickNDirty(), null))
                        .append("))\n");
            }

            sb.append("(check-sat)\n");

            ProcessBuilder pb = new ProcessBuilder("z3", "-T:3", "-in", "-smt2");
            Process process = pb.start();
            OutputStream out = process.getOutputStream();
            InputStream in = process.getInputStream();


            String smt = sb.toString();
            System.out.println(smt);
            out.write(smt.getBytes());
            out.close();

            BufferedReader br = new BufferedReader(new InputStreamReader(in));
            String line;
            while((line = br.readLine()) != null) {
                System.err.println("Z3: " + line);
                switch(line) {
                case "unsat":
                    return true;
                case "sat":
                    return false;
                case "unknown":
                    return false;
                }
            }

            // timeout
            return false;

        } catch (Exception ex) {
            ex.printStackTrace();
            return false;
        }
    }
}
