/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover;

import org.junit.runner.RunWith;
import org.junit.runners.Suite;
import org.junit.runners.Suite.SuiteClasses;

import edu.kit.iti.algover.parser.ParameterContractionVisitorTest;
import edu.kit.iti.algover.parser.ParserTest;
import edu.kit.iti.algover.parser.ReferenceResolutionVisitorTest;
import edu.kit.iti.algover.parser.TypeResolutionTest;
import edu.kit.iti.algover.project.ProjectTest;
import edu.kit.iti.algover.rules.impl.PropositionalExpanderTest;
import edu.kit.iti.algover.script.ScriptParserTest;
import edu.kit.iti.algover.symbex.ProgramDatabaseTest;
import edu.kit.iti.algover.symbex.SymbexTest;
import edu.kit.iti.algover.term.FunctionSymbolFamilyTest;
import edu.kit.iti.algover.term.SortTest;
import edu.kit.iti.algover.term.builder.InlineSequenterTest;
import edu.kit.iti.algover.term.builder.LetInlineVisitorTest;
import edu.kit.iti.algover.term.builder.ReplacementVisitorTest;
import edu.kit.iti.algover.term.builder.TreeTermTranslationNoetherTest;
import edu.kit.iti.algover.term.builder.TreeTermTranslatorTest;
import edu.kit.iti.algover.term.builder.UpdateSequenterTest;
import edu.kit.iti.algover.term.prettyprint.PrettyPrintTest;
import edu.kit.iti.algover.util.TestImmutableList;
import edu.kit.iti.algover.util.TestLabelIntroducer;
import edu.kit.iti.algover.util.UtilTest;

@RunWith(Suite.class)
@SuiteClasses({
    ParserTest.class,
    SymbexTest.class,
    ProgramDatabaseTest.class,
    TreeTermTranslatorTest.class,
    ReplacementVisitorTest.class,
    LetInlineVisitorTest.class,
    ParameterContractionVisitorTest.class,
    FunctionSymbolFamilyTest.class,
    TestImmutableList.class,
    TestLabelIntroducer.class,
    TreeTermTranslationNoetherTest.class,
//    DafnyTreeToDeclVisitorTest.class,
    ReferenceResolutionVisitorTest.class,
    TypeResolutionTest.class,
    SortTest.class,
    ProjectTest.class,
    ScriptParserTest.class,
    ProgramDatabaseTest.class,
    UtilTest.class,
    UpdateSequenterTest.class,
    InlineSequenterTest.class,
    PrettyPrintTest.class,
    PropositionalExpanderTest.class,
    })
public class Tests {
}
