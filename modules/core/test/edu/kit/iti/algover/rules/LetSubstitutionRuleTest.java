package edu.kit.iti.algover.rules;

import edu.kit.iti.algover.rules.impl.LetSubstitutionRule;
import org.junit.Test;

public class LetSubstitutionRuleTest {

    @Test
    public void testBasicSubstitution() throws Exception {
        ProofRule rule = new LetSubstitutionRule();
    }

    @Test
    public void testLetShadowing() throws Exception {

    }
}
