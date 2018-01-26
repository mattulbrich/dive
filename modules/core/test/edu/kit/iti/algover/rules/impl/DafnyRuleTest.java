package edu.kit.iti.algover.rules.impl;

import org.junit.Test;

/**
 * Created by jklamroth on 1/25/18.
 */
public class DafnyRuleTest {
    @Test
    public void initializationTest() {
        String dir = System.getProperty("user.dir");
        System.out.println("current dir = " + dir);
        String file = "./test-res/edu/kit/iti/algover/dafnyrules/addzero.dfy";
        DafnyRule r = new DafnyRule(file);
    }
}
