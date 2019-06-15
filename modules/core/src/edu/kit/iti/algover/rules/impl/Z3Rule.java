/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
// Checkstyle: ALLOFF

package edu.kit.iti.algover.rules.impl;

import edu.kit.iti.algover.dafnystructures.DafnyFunctionSymbol;
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
import edu.kit.iti.algover.smt.SExpr;
import edu.kit.iti.algover.smt.SMTQuickNDirty;
import edu.kit.iti.algover.term.FunctionSymbol;
import edu.kit.iti.algover.term.Sequent;
import edu.kit.iti.algover.term.Sort;
import edu.kit.iti.algover.util.Util;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileOutputStream;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.OutputStream;


/*
 * This is a quick and dirty implementation until the real one is available
 * Code quality is lower than elsewhere since this is a temporary implementation.
 */
public class Z3Rule extends AbstractProofRule {

    private static String SMT_TMP_DIR = System.getProperty("algover.smttmp");

    private static final String PREAMBLE =
            //"(define-fun seqlen ((a (Array Int Int))) Int (let ((x (select a (- 1)))) (ite (>= 0 x) x 0)))\n" +
            "(declare-sort Seqq 0)\n" +
            "(declare-fun seqget (Seqq Int) Int)\n" +
            "(declare-fun sequpd (Seqq Int Int) Seqq)\n" +
            "(declare-fun seqlen (Seqq) Int)\n" +
            "(declare-fun arrlen (Int) Int)\n" +
            "(assert (forall ((m Seqq)) (>= (seqlen m) 0)))\n" +
            "(assert (forall ((a Int)) (>= (arrlen a) 0)))\n" +
            "(assert (forall ((m Seqq)(i Int)(v Int)) (= (seqlen (sequpd m i v)) (seqlen m))))\n" +
            "(assert (forall ((m Seqq)(i Int)(v Int)(j Int)) (= (seqget (sequpd m i v) j) (ite (= i j) v (seqget m j)))))\n"
            ;

    @Override
    public String getName() {
        return "z3";
    }

    @Override
    public ProofRuleApplication considerApplicationImpl(ProofNode target, Parameters parameters) throws RuleException {
        ProofRuleApplicationBuilder builder = new ProofRuleApplicationBuilder(this);
        builder.setApplicability(Applicability.MAYBE_APPLICABLE);
        builder.setClosing();
        builder.setRefiner((app, param) -> refine(target, app));
        return builder.build();
    }

    private ProofRuleApplication refine(ProofNode target, ProofRuleApplication app) {
        if(quickAndDirty(target.getPVC().getIdentifier(), target.getSequent(), target.getAllSymbols())) {
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
    public ProofRuleApplication makeApplicationImpl(ProofNode target, Parameters parameters) throws RuleException {
        if(quickAndDirty(target.getPVC().getIdentifier(), target.getSequent(), target.getAllSymbols())) {
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

    private boolean quickAndDirty(String identifier, Sequent sequent, SymbolTable symbolTable) {

        StringBuilder sb = new StringBuilder();

        sb.append(PREAMBLE);

        try {
            for (FunctionSymbol fs : symbolTable.getAllSymbols()) {
                if (fs.getResultSort().equals(Sort.INT) && fs.getArity() == 0) {
                    sb.append("(declare-const pv$" + fs.getName() + " Int)\n");
                }
                if (fs.getResultSort().equals(Sort.get("seq", Sort.INT)) && fs.getArity() == 0) {
                    sb.append("(declare-const pv$" + fs.getName() + " Seqq)\n");
                }
                if (fs.getResultSort().equals(Sort.get("array", Sort.INT)) && fs.getArity() == 0) {
                    sb.append("(declare-const pv$" + fs.getName() + " Int)\n");
                }
                if (fs.getResultSort().equals(Sort.HEAP) && fs.getArity() == 0) {
                    sb.append("(declare-const pv$" + fs.getName() + " (Array Int Int Int))\n");
                }
                if (fs instanceof DafnyFunctionSymbol) {
                    DafnyFunctionSymbol dafnyFunctionSymbol = (DafnyFunctionSymbol) fs;
                    if (!dafnyFunctionSymbol.getOrigin().isDeclaredInClass()
                            && dafnyFunctionSymbol.getArgumentSorts().stream().
                                 allMatch(x -> x.equals(Sort.INT) || x.equals(Sort.HEAP))
                            && dafnyFunctionSymbol.getResultSort().equals(Sort.INT)) {
                        sb.append("(declare-fun func" + fs.getName() + " ((Array Int Int Int)")
                                .append(Util.duplicate(" Int", fs.getArity() - 1))
                                .append(") Int)");
                    }
                }
            }
            for (ProofFormula proofFormula : sequent.getAntecedent()) {
                try {
                    SExpr trans = proofFormula.getTerm().accept(new SMTQuickNDirty(), null);
                    sb.append("(assert ")
                            .append(trans)
                            .append(")\n");
                } catch(UnsupportedOperationException ex) {
                    sb.append("; unsupported (" + ex + "): " + proofFormula + "\n");
                }
            }
            for (ProofFormula proofFormula : sequent.getSuccedent()) {
                try {
                    SExpr trans = proofFormula.getTerm().accept(new SMTQuickNDirty(), null);
                    sb.append("(assert (not ")
                            .append(trans)
                            .append("))\n");
                } catch(UnsupportedOperationException ex) {
                    sb.append("; unsupported " + proofFormula + "\n");
                }
            }

            sb.append("(check-sat)\n");

            ProcessBuilder pb = new ProcessBuilder("z3", "-T:3", "-in", "-smt2");
            Process process = pb.start();
            OutputStream out = process.getOutputStream();
            InputStream in = process.getInputStream();

            String smt = sb.toString();
            if(SMT_TMP_DIR != null) {
                File f = new File(SMT_TMP_DIR, System.currentTimeMillis() + identifier.replaceAll("/","+") + ".smt2");
                FileOutputStream fos = new FileOutputStream(f);
                fos.write(smt.getBytes());
                fos.close();
            }

            // System.out.println(smt);
            out.write(smt.getBytes());
            out.close();

            BufferedReader br = new BufferedReader(new InputStreamReader(in));
            String line;
            while((line = br.readLine()) != null) {
                // System.err.println("Z3: " + line);
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
