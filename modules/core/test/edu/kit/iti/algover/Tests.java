/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2016 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover;

import org.junit.runner.RunWith;
import org.junit.runners.Suite;
import org.junit.runners.Suite.SuiteClasses;

import edu.kit.iti.algover.parser.ParserTest;
import edu.kit.iti.algover.symbex.ProgramDatabaseTest;
import edu.kit.iti.algover.symbex.SymbexTest;
import edu.kit.iti.algover.term.builder.TreeTermTranslationNoetherTest;
import edu.kit.iti.algover.term.builder.TreeTermTranslatorTest;
import edu.kit.iti.algover.util.TestImmutableList;
import edu.kit.iti.algover.util.TestLabelIntroducer;
import edu.kit.iti.algover.util.TestUtil;

@RunWith(Suite.class)
@SuiteClasses({ParserTest.class,
    SymbexTest.class,
    ProgramDatabaseTest.class,
    TreeTermTranslatorTest.class,
    TestImmutableList.class,
    TestLabelIntroducer.class,
    TreeTermTranslationNoetherTest.class,
    })
public class Tests {
}
