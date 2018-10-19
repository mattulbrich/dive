/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover;

import edu.kit.iti.algover.dafnystructures.DafnyTreeToDeclVisitorTest;
import edu.kit.iti.algover.dafnystructures.TarjansAlgorithmTest;
import edu.kit.iti.algover.parser.ChainedRelationsVisitorTest;
import edu.kit.iti.algover.parser.ImplicitlyTypedVariableVisitorTest;
import edu.kit.iti.algover.parser.ModifiesListResolverTest;
import edu.kit.iti.algover.parser.ParserErrorTest;
import edu.kit.iti.algover.parser.QuantifierGuardRemovalVisitorTest;
import edu.kit.iti.algover.project.ProjectManagerTest;
import edu.kit.iti.algover.proof.PVCBuilderTest;
import edu.kit.iti.algover.proof.ProofTest;
import edu.kit.iti.algover.references.TermReferencesBuilderTest;
import edu.kit.iti.algover.rules.impl.CutRuleTest;
import edu.kit.iti.algover.rules.impl.DafnyRuleTest;
import edu.kit.iti.algover.rules.impl.FunctionDefinitionExpansionRuleTest;
import edu.kit.iti.algover.rules.impl.GenericRuleTest;
import edu.kit.iti.algover.rules.impl.LetSubstitutionRuleTest;
import edu.kit.iti.algover.rules.impl.NotLeftRuleTest;
import edu.kit.iti.algover.rules.impl.OrLeftRuleTest;
import edu.kit.iti.algover.rules.impl.PropositionalExpanderTest;
import edu.kit.iti.algover.symbex.FunctionObligationMakerTest;
import edu.kit.iti.algover.symbex.SymbexExpressionValidatorTest;
import edu.kit.iti.algover.term.builder.ParallelUpdateSequenterTest;
import edu.kit.iti.algover.term.builder.ReplaceVisitorTest;
import edu.kit.iti.algover.term.builder.SSASequenterTest;
import edu.kit.iti.algover.term.builder.SimplifiedUpdateSequenterTest;
import edu.kit.iti.algover.term.builder.TreeAssignmentTranslatorTest;
import edu.kit.iti.algover.util.RuleUtilTest;
import org.junit.runner.RunWith;
import org.junit.runners.Suite;
import org.junit.runners.Suite.SuiteClasses;

import edu.kit.iti.algover.integration.IntegrationTest1;
import edu.kit.iti.algover.parser.ParameterContractionVisitorTest;
import edu.kit.iti.algover.parser.ParserTest;
import edu.kit.iti.algover.parser.ReferenceResolutionVisitorTest;
import edu.kit.iti.algover.parser.TypeResolutionTest;
import edu.kit.iti.algover.project.ProjectTest;
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
import edu.kit.iti.algover.term.match.TermMatcherTest;
import edu.kit.iti.algover.term.prettyprint.PrettyPrintTest;
import edu.kit.iti.algover.util.TestImmutableList;
import edu.kit.iti.algover.util.TestLabelIntroducer;
import edu.kit.iti.algover.util.UtilTest;

@RunWith(Suite.class)
@SuiteClasses({
    ParserTest.class,
    ParserErrorTest.class,
    SymbexTest.class,
    SymbexExpressionValidatorTest.class,
    FunctionObligationMakerTest.class,
    ProgramDatabaseTest.class,
    TreeTermTranslatorTest.class,
    TreeAssignmentTranslatorTest.class,
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
        ProofTest.class,
    ScriptParserTest.class,
        ProjectManagerTest.class,
    ProgramDatabaseTest.class,
    UtilTest.class,
    DafnyRuleTest.class,
    GenericRuleTest.class,
    SimplifiedUpdateSequenterTest.class,
    UpdateSequenterTest.class,
    ParallelUpdateSequenterTest.class,
    InlineSequenterTest.class,
    SSASequenterTest.class,
    PVCBuilderTest.class,
    TarjansAlgorithmTest.class,
    PrettyPrintTest.class,
    TermReferencesBuilderTest.class,
    IntegrationTest1.class,
    LetSubstitutionRuleTest.class,
    TermMatcherTest.class,
    ChainedRelationsVisitorTest.class,
    ImplicitlyTypedVariableVisitorTest.class,
    QuantifierGuardRemovalVisitorTest.class,
    ModifiesListResolverTest.class,
    CutRuleTest.class,
    NotLeftRuleTest.class,
    OrLeftRuleTest.class,
    PropositionalExpanderTest.class,
    FunctionDefinitionExpansionRuleTest.class,
    ReplacementVisitorTest.class,
    ReplaceVisitorTest.class,
        RuleUtilTest.class
    })
public class Tests {
}
