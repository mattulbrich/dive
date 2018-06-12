/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 *
 */

// Checkstyle: ALLOFF

package edu.kit.iti.algover.rules.impl;

import edu.kit.iti.algover.data.SymbolTable;
import edu.kit.iti.algover.parser.DafnyTree;
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
import edu.kit.iti.algover.smttrans.access.SolverAccess;
import edu.kit.iti.algover.smttrans.access.Z3Access;
import edu.kit.iti.algover.smttrans.data.SMTContainer;
import edu.kit.iti.algover.smttrans.translate.SMTTerm;
import edu.kit.iti.algover.smttrans.translate.SMTVisitor;
import edu.kit.iti.algover.smttrans.translate.TypeContext;
import edu.kit.iti.algover.smttrans.translate.expressions.SMTExpression;
import edu.kit.iti.algover.term.FunctionSymbol;
import edu.kit.iti.algover.term.Sequent;
import edu.kit.iti.algover.term.Sort;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileOutputStream;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.OutputStream;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Set;

/*
 * This is a quick and dirty implementation until the real one is available
 * Code quality is lower than elsewhere since this is a temporary implementation.
 */
public class Z3Rule extends AbstractProofRule {

    private static String SMT_TMP_DIR = System.getProperty("algover.smttmp");

    private static final String PREAMBLE =
            // "(define-fun seqlen ((a (Array Int Int))) Int (let ((x (select a (- 1))))
            // (ite (>= 0 x) x 0)))\n" +
            "(declare-sort Seqq 0)\n" + "(declare-fun seqget (Seqq Int) Int)\n"
                    + "(declare-fun sequpd (Seqq Int Int) Seqq)\n" + "(declare-fun seqlen (Seqq) Int)\n"
                    + "(assert (forall ((m Seqq)) (>= (seqlen m) 0)))\n"
                    + "(assert (forall ((m Seqq)(i Int)(v Int)) (= (seqlen (sequpd m i v)) (seqlen m))))\n"
                    + "(assert (forall ((m Seqq)(i Int)(v Int)(j Int)) (= (seqget (sequpd m i v) j) (ite (= i j) v (seqget m j)))))\n";

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
       // System.out.println("PVC: " + target.getPVC().getSequent().toString());
        //SolverAccess.evaluate("");
        Z3Access z3 = new Z3Access();
        z3.accessSolver();
        PVC pvc = target.getPVC();
        Map<TermSelector, DafnyTree> referenceMap = pvc.getReferenceMap();
        SMTContainer sc = translateToSMT(target.getPVC().getIdentifier(), target.getSequent(), pvc.getSymbolTable(),
                referenceMap);
        // String smtlib = translateToSMT(target.getPVC().getIdentifier(),
        // target.getSequent(), pvc.getSymbolTable()).toPSMT();
        // System.out.println(sc.toPSMT());
        // System.out.println(" ");
        // System.out.println(" ");
        // System.out.println(" ");
        
        //System.out.println(sc.toSMT());
        //System.out.println(sc.toPSMT());
        
        // if(quickAndDirty(target.getPVC().getIdentifier(), target.getSequent(),
        // pvc.getSymbolTable())) {
        // ProofRuleApplicationBuilder builder = new ProofRuleApplicationBuilder(app);
        // builder.setApplicability(Applicability.APPLICABLE);
        // builder.setRefiner(null);
        // return builder.build();
        // } else {
        // ProofRuleApplicationBuilder builder = new ProofRuleApplicationBuilder(app);
        // builder.setApplicability(Applicability.NOT_APPLICABLE);
        // builder.setRefiner(null);
        // return builder.build();
        // }
        return null;
    }

    private SMTContainer translateToSMT(String identifier, Sequent sequent, SymbolTable symbolTable,
            Map<TermSelector, DafnyTree> refs) {
         //TODO symbolTable not needed ?
        
       

        

        // System.out.println(symbolTable.getAllSymbols().toString());

//        for (FunctionSymbol fs : symbolTable.getAllSymbols()) {
//            if (!fs.getName().startsWith("$")) {
//                System.out.println("FS " + fs.getName());
//                System.out.println(fs.getResultSort().getName());
//            }
//        }

        List<ProofFormula> antecedent = sequent.getAntecedent();
        List<ProofFormula> succedent = sequent.getSuccedent();

        List<SMTTerm> aTerms = new ArrayList<>();
        List<SMTTerm> sTerms = new ArrayList<>();

      //  System.out.println(symbolTable.getAllSymbols().toString());

        for (ProofFormula pa : antecedent) {
         //   System.out.println("Label: " + pa.getLabel());

            SMTExpression e = pa.getTerm().accept(new SMTVisitor(), null);
            SMTTerm t = new SMTTerm(e);
            aTerms.add(t);

        }
        for (ProofFormula ps : succedent) {
            // negate
            SMTExpression e = ps.getTerm().accept(new SMTVisitor(), null);
            SMTTerm t = new SMTTerm(e);
            sTerms.add(t);

        }
        
      //  System.out.println(TypeContext.getSymbolTable().getAllSymbols().toString()) ;

        return new SMTContainer(aTerms, sTerms);
    }

    @Override
    public ProofRuleApplication makeApplicationImpl(ProofNode target, Parameters parameters) throws RuleException {
        PVC pvc = target.getPVC();

        if (quickAndDirty(target.getPVC().getIdentifier(), target.getSequent(), pvc.getSymbolTable())) {
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
            }
            for (ProofFormula proofFormula : sequent.getAntecedent()) {
                sb.append("(assert ").append(proofFormula.getTerm().accept(new SMTQuickNDirty(), null)).append(")\n");
            }
            for (ProofFormula proofFormula : sequent.getSuccedent()) {
                sb.append("(assert (not ").append(proofFormula.getTerm().accept(new SMTQuickNDirty(), null))
                        .append("))\n");
            }

            sb.append("(check-sat)\n");

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

            // System.out.println(smt);
            out.write(smt.getBytes());
            out.close();

            BufferedReader br = new BufferedReader(new InputStreamReader(in));
            String line;
            while ((line = br.readLine()) != null) {
                // System.err.println("Z3: " + line);
                switch (line) {
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
