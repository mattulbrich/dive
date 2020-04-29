/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 *
 */

package edu.kit.iti.algover.rules;

import edu.kit.iti.algover.data.BuiltinSymbols;
import edu.kit.iti.algover.proof.ProofFormula;
import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.term.SchemaVarTerm;
import edu.kit.iti.algover.term.Sequent;
import edu.kit.iti.algover.term.builder.TermBuildException;
import edu.kit.iti.algover.term.builder.TermBuilder;
import org.junit.Test;

import java.math.BigInteger;

import static org.junit.Assert.*;

// Caution: There is also AbstractRuleTest!

public class AbstractProofRuleTest {

    private static final ParameterDescription<BigInteger> OPT_INT_PARAM =
            new ParameterDescription<>("optionalInt", ParameterType.INTEGER, false);
    private static final ParameterDescription<Boolean> OPT_BOOL_PARAM =
            new ParameterDescription<>("optionalBool", ParameterType.BOOLEAN, false);
    private static final ParameterDescription<String> OPT_STRING_PARAM =
            new ParameterDescription<>("optionalString", ParameterType.STRING, false);
    private static final ParameterDescription<TermParameter> OPT_TERM_PARAM =
            new ParameterDescription<>("optionalTerm", ParameterType.TERM, false);
    public static final TestRule RULE = new TestRule();

    private static class TestRule extends NoFocusProofRule {

        TestRule() {
            super(OPT_INT_PARAM, OPT_BOOL_PARAM, OPT_STRING_PARAM, OPT_TERM_PARAM);
        }

        @Override
        protected ProofRuleApplication makeApplicationImpl(ProofNode target, Parameters parameters) throws RuleException {
            throw new Error();
        }

        @Override
        public String getName() {
            return "testRule";
        }
    }

    @Test
    public void getTranscript1() throws RuleException {

        ProofRuleApplicationBuilder prab = new ProofRuleApplicationBuilder(RULE);
        Parameters ps = new Parameters();
        prab.setParameters(ps);

        assertEquals("testRule;", RULE.getTranscript(prab.build()));
    }

    @Test
    public void getTranscript2() throws RuleException, TermBuildException {

        TermBuilder tb = new TermBuilder(new BuiltinSymbols());
        Sequent s = Sequent.singleSuccedent(new ProofFormula(tb.tt()));

        ProofRuleApplicationBuilder prab = new ProofRuleApplicationBuilder(RULE);
        Parameters ps = new Parameters();
        ps.putValue(OPT_BOOL_PARAM, true);
        ps.putValue(OPT_INT_PARAM, BigInteger.valueOf(42));
        ps.putValue(OPT_STRING_PARAM, "43");
        ps.putValue(OPT_TERM_PARAM, new TermParameter(tb.tt(), s));
        prab.setParameters(ps);

        assertEquals("testRule optionalBool=true optionalInt=42 " +
                        "optionalString=\"43\" optionalTerm='true';",
                RULE.getTranscript(prab.build()));
    }

    @Test
    public void getTranscript3() throws RuleException, TermBuildException {

        TermBuilder tb = new TermBuilder(new BuiltinSymbols());
        Sequent s = Sequent.singleSuccedent(new ProofFormula(tb.tt()));

        ProofRuleApplicationBuilder prab = new ProofRuleApplicationBuilder(RULE);
        Parameters ps = new Parameters();
        ps.putValue(OPT_TERM_PARAM, new TermParameter(
                Sequent.singleSuccedent(new ProofFormula(
                        new SchemaVarTerm("_"))), s));
        prab.setParameters(ps);

        assertEquals("testRule optionalTerm='|- _';",
                RULE.getTranscript(prab.build()));
    }

    @Test
    public void getTranscript4() throws RuleException, TermBuildException {

        ProofRuleApplicationBuilder prab = new ProofRuleApplicationBuilder(RULE);
        Parameters ps = new Parameters();
        prab.setParameters(ps);

        prab.newBranch().setLabel("label1");
        prab.newBranch().setLabel("label2");

        assertEquals("testRule;\n" +
                        "cases {\n" +
                        "\tcase match \"label1\": \n" +
                        "\n" +
                        "\tcase match \"label2\": \n" +
                        "\n" +
                        "}\n",
                RULE.getTranscript(prab.build()));
    }
}