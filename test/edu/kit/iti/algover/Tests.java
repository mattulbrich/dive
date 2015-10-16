package edu.kit.iti.algover;

import org.junit.runner.RunWith;
import org.junit.runners.Suite;
import org.junit.runners.Suite.SuiteClasses;

import edu.kit.iti.algover.parser.ParserTest;
import edu.kit.iti.algover.symbex.ProgramDatabaseTest;
import edu.kit.iti.algover.symbex.SymbexTest;

@RunWith(Suite.class)
@SuiteClasses({ParserTest.class, SymbexTest.class, ProgramDatabaseTest.class})
public class Tests {
}
