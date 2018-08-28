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
import edu.kit.iti.algover.smttrans.access.CVCAccess;
import edu.kit.iti.algover.smttrans.access.MathSATAccess;
import edu.kit.iti.algover.smttrans.access.Model;
import edu.kit.iti.algover.smttrans.access.Response;
import edu.kit.iti.algover.smttrans.access.SMTLog;
import edu.kit.iti.algover.smttrans.access.SolverAccess;
import edu.kit.iti.algover.smttrans.access.SolverParameter;
import edu.kit.iti.algover.smttrans.access.SolverResponse;
import edu.kit.iti.algover.smttrans.access.YicesAccess;
import edu.kit.iti.algover.smttrans.access.Z3Access;
import edu.kit.iti.algover.smttrans.data.AxiomContainer;
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

/*
 * This is a quick and dirty implementation until the real one is available
 * Code quality is lower than elsewhere since this is a temporary implementation.
 */
public class Z3Rule extends AbstractProofRule {

    private static Model model = new Model(new ArrayList<>()); // empty model

    public static Model getModel() {
        return model;
    }

    @Override
    public String getName() {
        return "z3";
    }

    @Override
    public ProofRuleApplication considerApplicationImpl(ProofNode target, Parameters parameters) throws RuleException {
        ProofRuleApplicationBuilder builder = new ProofRuleApplicationBuilder(this);
        // TODO change ?
        // builder.setApplicability(Applicability.MAYBE_APPLICABLE);
        builder.setApplicability(Applicability.APPLICABLE);
        builder.setClosing();
        builder.setRefiner((app, param) -> refine(target, app));
        return builder.build();
    }

    private ProofRuleApplication refine(ProofNode target, ProofRuleApplication app) {
        PVC pvc = target.getPVC();

        if (isValid(target)) {
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

        if (isValid(target)) {
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

    private boolean isValid(ProofNode target) {
        System.out.println("PVC: " + target.getPVC().getSequent().toString());
        // SolverAccess.evaluate("");
        SolverAccess z3access = new Z3Access();
        SolverAccess cvcaccess = new CVCAccess();
        SolverAccess msaccess = new MathSATAccess();
        SolverAccess yicesaccess = new YicesAccess();
        PVC pvc = target.getPVC();
        // System.out.println("ID " + pvc.getIdentifier());

        SMTContainer sc = translateToSMT(target.getSequent(), pvc.getSymbolTable());

        String smt;

        smt = sc.toPSMT();
        // SMTLog.writeFile(smt, pvc.getIdentifier()+".psmt");
        //TypeContext.reset();
      //  System.out.println(smt);
     //  AxiomContainer.reset();
        smt = sc.toSMT();

        // SMTLog.writeFile(smt, pvc.getIdentifier()+".smt2");
        //
        // System.out.println();
     //   System.out.println(smt);

        SolverParameter p = new SolverParameter(smt, 8, true);
        SolverResponse r1 = z3access.accessSolver(p);
        // SolverResponse r1 = msaccess.accessSolver(p);
        // SolverResponse r1 = yicesaccess.accessSolver(p);
        // SolverResponse r1 = cvcaccess.accessSolver(p);

        System.out.println(r1.getResponse().name());
        if (r1.getResponse() == Response.SAT) {
            model = r1.getModel();
            // System.out.println(model.getDeclarations());
            // System.out.println(model.getDefinitions());
            // model.printVars();
        }

        // System.out.println(r1.getModel().toString());
        TypeContext.reset();
        return evaluate(r1.getResponse());
    }

    private boolean evaluate(Response r) {
        switch (r) {
        case UNSAT:
            return true;

        default:
            return false;
        }
    }

    public String testRule(Sequent sequent, SymbolTable symbolTable) {

        SMTContainer container = translateToSMT(sequent, symbolTable);
        String smt = container.toSMT();
        TypeContext.reset();

        return smt;
    }

    private SMTContainer translateToSMT(Sequent sequent, SymbolTable symbolTable) {

        List<ProofFormula> antecedent = sequent.getAntecedent();
        List<ProofFormula> succedent = sequent.getSuccedent();

        List<SMTTerm> aTerms = new ArrayList<>();
        List<SMTTerm> sTerms = new ArrayList<>();

        for (ProofFormula pa : antecedent) {

            SMTExpression e = pa.getTerm().accept(new SMTVisitor(), null);
            SMTTerm t = new SMTTerm(e);
            aTerms.add(t);

        }
        for (ProofFormula ps : succedent) {

            SMTExpression e = ps.getTerm().accept(new SMTVisitor(), null);
            SMTTerm t = new SMTTerm(e);
            sTerms.add(t);

        }

        return new SMTContainer(aTerms, sTerms);
    }

}