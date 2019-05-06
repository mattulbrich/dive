package edu.kit.iti.algover.references;

import com.google.common.graph.EndpointPair;
import edu.kit.iti.algover.data.BuiltinSymbols;
import edu.kit.iti.algover.parser.DafnyParserException;
import edu.kit.iti.algover.proof.Proof;
import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.proof.ProofNodeSelector;
import edu.kit.iti.algover.rules.RuleException;
import edu.kit.iti.algover.rules.TermSelector;
import edu.kit.iti.algover.term.*;
import edu.kit.iti.algover.term.builder.TermBuildException;
import edu.kit.iti.algover.util.FormatException;
import edu.kit.iti.algover.util.TestUtil;
import org.junit.Assert;
import org.junit.Test;

import static edu.kit.iti.algover.util.ProofMockUtil.mockProofNode;

public class TermReferencesBuilderTest {

    private final Proof proof;
    private final ProofNode before;
    private final ProofNode after;
    private final ProofNodeSelector afterReference;
    private final ReferenceGraph graph;
    private final TermReferencesBuilder builder;


    public TermReferencesBuilderTest() throws TermBuildException, DafnyParserException, RuleException, FormatException {
        Term x = new VariableTerm("x", Sort.INT);
        Term y = new VariableTerm("y", Sort.INT);
        Term xEqY = new ApplTerm(BuiltinSymbols.EQ.instantiate(Sort.INT), x, y);
        Term yEqX = new ApplTerm(BuiltinSymbols.EQ.instantiate(Sort.INT), y, x);

        proof = new Proof(null, null);
        before = mockProofNode(null, new Term[]{xEqY}, new Term[0]);
        after = mockProofNode(before, new Term[]{yEqX, xEqY}, new Term[0]);
        afterReference = new ProofNodeSelector((byte) 0);

        before.getChildren().add(after);
        TestUtil.setField(proof, "proofRoot", before);

        graph = new ReferenceGraph();
        builder = new TermReferencesBuilder(graph, proof, new ProofNodeSelector());
        builder.buildReferences(afterReference, new TermSelector("A.0"));
    }

    @Test
    public void builderCreatesEdges() {
        System.out.println("computed graph:");
        System.out.println(graph);
        Assert.assertEquals(
                "The graph should have 5 reference edges",
                5, graph.getGraph().edges().size());
    }

    @Test
    public void referencesBuiltAreValid() {
        ValidityTester tester = new ValidityTester();
        boolean allReferencesValid = true;

        for (ReferenceTarget reference : graph.getGraph().nodes()) {
            allReferencesValid &= reference.accept(tester);

        }
        Assert.assertTrue("All references should be valid", allReferencesValid);
    }

    private class ValidityTester implements ReferenceTargetVisitor<Boolean> {
        @Override
        public Boolean visit(CodeReferenceTarget codeTarget) {
            return false; // This should not be generated by our test!
        }

        @Override
        public Boolean visit(ProofTermReferenceTarget termTarget) {
            try {
                ProofNode node = termTarget.getProofNodeSelector().get(proof);
                termTarget.getTermSelector().selectSubterm(node.getSequent());
                return true;
            } catch (RuleException e) {
                // when our selector(s) are invalid!
                return false;
            }
        }

        @Override
        public Boolean visit(UserInputReferenceTarget userInputTarget) {
            return true;
        }

        @Override
        public Boolean visit(ScriptReferenceTarget scriptReferenceTarget) {
            return false;
        }

    }

    // This test is more like meant to be used for figuring out mistakes by eye,
    // in case the other tests fail
    @Test
    public void prettyPrintReferences() {
        ReferencePrettyPrinter prettyPrinter = new ReferencePrettyPrinter(proof, 80);
        int i = 0;
        for (EndpointPair<ReferenceTarget> referenceEdge : graph.getGraph().edges()) {
            System.out.println(i++ + " ---------------------------------------------");
            System.out.println(referenceEdge.nodeU().accept(prettyPrinter));
            System.out.println("\n    =>\n");
            System.out.println(referenceEdge.nodeV().accept(prettyPrinter));
        }
    }
}