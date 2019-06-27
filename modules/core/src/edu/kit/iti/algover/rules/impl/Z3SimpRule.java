/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 *
 */
// Checkstyle: ALLOFF

package edu.kit.iti.algover.rules.impl;

import de.uka.ilkd.pp.NoExceptions;
import edu.kit.iti.algover.dafnystructures.DafnyFunctionSymbol;
import edu.kit.iti.algover.data.BuiltinSymbols;
import edu.kit.iti.algover.data.SymbolTable;
import edu.kit.iti.algover.proof.ProofFormula;
import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.rules.FocusProofRule;
import edu.kit.iti.algover.rules.NotApplicableException;
import edu.kit.iti.algover.rules.ParameterDescription;
import edu.kit.iti.algover.rules.ParameterType;
import edu.kit.iti.algover.rules.Parameters;
import edu.kit.iti.algover.rules.ProofRuleApplication;
import edu.kit.iti.algover.rules.ProofRuleApplication.Applicability;
import edu.kit.iti.algover.rules.ProofRuleApplicationBuilder;
import edu.kit.iti.algover.rules.RuleException;
import edu.kit.iti.algover.rules.TermSelector;
import edu.kit.iti.algover.smt.SExpr;
import edu.kit.iti.algover.smt.SMTQuickNDirty;
import edu.kit.iti.algover.term.ApplTerm;
import edu.kit.iti.algover.term.FunctionSymbol;
import edu.kit.iti.algover.term.Sequent;
import edu.kit.iti.algover.term.Sort;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.term.TermVisitor;
import edu.kit.iti.algover.term.builder.TermBuildException;
import edu.kit.iti.algover.term.builder.TermBuilder;
import edu.kit.iti.algover.util.Util;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileOutputStream;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.OutputStream;
import java.util.List;

/**
 * This class implements a rule that uses z3 to simplify an expression.
 *
 * Currently it is tailored for integer simplification only, but should be
 * eventually generalised.
 *
 * see also the
 * <a href="https://rise4fun.com/Z3/dy3?frame=1&menu=0&course=1">Z3 tutorial</a>.
 *
 * @author Mattias Ulbrich
 *
 * @see Z3Rule
 */
public class Z3SimpRule extends FocusProofRule {

    /**
     * This parameter allows one to add simplification parameters for z3.
     */
    private static final ParameterDescription<String> CONFIG_PARAM =
            new ParameterDescription<>("config", ParameterType.STRING, false);

    // see Z3Rule
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
        return "z3simp";
    }

    public Z3SimpRule() {
        super(CONFIG_PARAM);
    }

    @Override
    public ProofRuleApplication makeApplicationImpl(ProofNode target, Parameters parameters) throws RuleException {
        ProofRuleApplicationBuilder builder = new ProofRuleApplicationBuilder(this);
        builder.setApplicability(Applicability.MAYBE_APPLICABLE);
        builder.setRefiner((app, param) -> refine(target, parameters, app));
        return builder.build();
    }

    private ProofRuleApplication refine(ProofNode target, Parameters params, ProofRuleApplication app) throws RuleException {

        TermSelector on = params.getValue(ON_PARAM).getTermSelector();
        Term onTerm = on.selectSubterm(target.getSequent());
        String config = params.getValueOrDefault(CONFIG_PARAM, "");

        Term replacement = z3Simplify(target.getPVC().getIdentifier(), target.getSequent(), on, config, target.getAllSymbols());

        if (replacement.equals(onTerm)) {
            throw new NotApplicableException("The simplification does not change the term");
        } else {
            ProofRuleApplicationBuilder builder = new ProofRuleApplicationBuilder(app);
            builder.setApplicability(Applicability.APPLICABLE);
            builder.newBranch().addReplacement(on, replacement);
            builder.setRefiner(null);
            builder.setParameters(params);
            return builder.build();
        }

    }

    private Term z3Simplify(String identifier, Sequent sequent, TermSelector on, String config, SymbolTable symbolTable) throws RuleException {

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

            int no = 0;
            for (ProofFormula proofFormula : sequent.getAntecedent()) {
                if (on.isAntecedent() && on.getTermNo() == no) {
                    continue;
                }
                try {
                    SExpr trans = proofFormula.getTerm().accept(new SMTQuickNDirty(), null);
                    sb.append("(assert ")
                            .append(trans)
                            .append(")\n");
                } catch (UnsupportedOperationException ex) {
                    sb.append("; unsupported (" + ex + "): " + proofFormula + "\n");
                }
                no++;
            }

            no = 0;
            for (ProofFormula proofFormula : sequent.getSuccedent()) {
                if (on.isSuccedent() && on.getTermNo() == no) {
                    continue;
                }
                try {
                    SExpr trans = proofFormula.getTerm().accept(new SMTQuickNDirty(), null);
                    sb.append("(assert (not ")
                            .append(trans)
                            .append("))\n");
                } catch (UnsupportedOperationException ex) {
                    sb.append("; unsupported " + proofFormula + "\n");
                }
                no++;
            }

            Term selected = on.selectSubterm(sequent);
            Z3SimpPullOutVisitor pullOut = new Z3SimpPullOutVisitor();
            String pulledOutSMT = selected.accept(pullOut, sb);

            sb.append(String.format("(simplify %s %s)%n", pulledOutSMT, config));

            ProcessBuilder pb = new ProcessBuilder("z3", "-T:3", "-in", "-smt2");
            Process process = pb.start();
            OutputStream out = process.getOutputStream();
            InputStream in = process.getInputStream();

            String smt = sb.toString();
            if (SMT_TMP_DIR != null) {
                File f = new File(SMT_TMP_DIR, System.currentTimeMillis() + identifier.replaceAll("/", "+") + ".smt2");
                FileOutputStream fos = new FileOutputStream(f);
                fos.write(smt.getBytes());
                fos.close();
            }

            System.out.println(smt);
            out.write(smt.getBytes());
            out.close();

            BufferedReader br = new BufferedReader(new InputStreamReader(in));
            String line;
            while ((line = br.readLine()) != null) {
                System.err.println("Z3: " + line);
            }

            List<Term> placeholderList = pullOut.getReplacedTerms();

            // TODO PARSE THE Z3 OUTPUT and regenerate the term using the replacement map
            // placeholder_7 must be replaced by placeholderList.get(7)
            // + must be replaced by BuiltinSymbols.PLUS
            // having a reverse list for the list in the visitor seems sensible.

            // Fake result
            return new TermBuilder(symbolTable).zero;

        } catch (RuleException ex) {
            throw ex;
        } catch (Exception ex) {
            throw new RuleException(ex);
        }
    }
}
