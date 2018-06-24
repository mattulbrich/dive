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
import edu.kit.iti.algover.smttrans.access.Response;
import edu.kit.iti.algover.smttrans.access.SolverAccess;
import edu.kit.iti.algover.smttrans.access.SolverParameter;
import edu.kit.iti.algover.smttrans.access.SolverResponse;
import edu.kit.iti.algover.smttrans.access.Z3Access;
import edu.kit.iti.algover.smttrans.data.SMTContainer;
import edu.kit.iti.algover.smttrans.translate.SMTTerm;
import edu.kit.iti.algover.smttrans.translate.SMTVisitor;
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

    @Override
    public String getName() {
        return "z3";
    }

    @Override
    public ProofRuleApplication considerApplicationImpl(ProofNode target, Parameters parameters) throws RuleException {
        ProofRuleApplicationBuilder builder = new ProofRuleApplicationBuilder(this);
        //TODO change ?
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
        PVC pvc = target.getPVC();

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
      //  System.out.println("PVC: " + target.getPVC().getSequent().toString());
        // SolverAccess.evaluate("");
        SolverAccess z3access = new Z3Access();
        SolverAccess cvcaccess = new CVCAccess();
        PVC pvc = target.getPVC();

        SMTContainer sc = translateToSMT(target.getPVC().getIdentifier(), target.getSequent(), pvc.getSymbolTable());

        String smt;
        // System.out.println();
        // System.out.println();
        // System.out.println("PSMT: ");
        // System.out.println();
        // smt = sc.toPSMT();
        // System.out.println(smt);
        // System.out.println();
        // System.out.println();

//        System.out.println("SMT: ");
//        System.out.println();
        smt = sc.toSMT();
//        System.out.println(smt);
//
//        System.out.println();

        SolverParameter p = new SolverParameter(smt,3, true);
        SolverResponse r1 = z3access.accessSolver(p);

        // SolverResponse r2 = cvcaccess.accessSolver(sc.toSMT().replace("Null",
        // "ArrInt").replace("setcardT","setcardInt").replace("setEmptyT",
        // "setEmptyInt"));

        System.out.println(r1.getResponse().name());

        //if (r1.getResponse() == Response.SAT)
          //  System.out.println(r1.getModel().toString());

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

    private SMTContainer translateToSMT(String identifier, Sequent sequent, SymbolTable symbolTable) {

        List<ProofFormula> antecedent = sequent.getAntecedent();
        List<ProofFormula> succedent = sequent.getSuccedent();

        List<SMTTerm> aTerms = new ArrayList<>();
        List<SMTTerm> sTerms = new ArrayList<>();

        // System.out.println(symbolTable.getAllSymbols().toString());

        for (ProofFormula pa : antecedent) {
            // System.out.println("Label: " + pa.getLabel());

            SMTExpression e = pa.getTerm().accept(new SMTVisitor(), null);
            SMTTerm t = new SMTTerm(e);
            aTerms.add(t);

        }
        for (ProofFormula ps : succedent) {

            SMTExpression e = ps.getTerm().accept(new SMTVisitor(), null);
            SMTTerm t = new SMTTerm(e);
            sTerms.add(t);

        }

        // System.out.println(TypeContext.getSymbolTable().getAllSymbols().toString()) ;

        return new SMTContainer(aTerms, sTerms);
    }

}