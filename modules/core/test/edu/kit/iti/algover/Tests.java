/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover;

import org.junit.runner.RunWith;
import org.junit.runners.Suite;
import org.junit.runners.Suite.SuiteClasses;

import edu.kit.iti.algover.smt.SMTTest;
import edu.kit.iti.smttrans.access.Z3AccessTest;
import edu.kit.iti.smttrans.translate.Arr1Test;
import edu.kit.iti.smttrans.translate.ClassTest;
import edu.kit.iti.smttrans.translate.FolTest;
import edu.kit.iti.smttrans.translate.IntegerTest;
import edu.kit.iti.smttrans.translate.SeqTest;
import edu.kit.iti.smttrans.translate.SetTest;
import edu.kit.iti.smttrans.translate.SumAndMaxTest;

@RunWith(Suite.class)
@SuiteClasses({

//    ParserTest.class,
//    ParserErrorTest.class,
//    SymbexTest.class,
//    ProgramDatabaseTest.class,
//    TreeTermTranslatorTest.class,
//    TreeAssignmentTranslatorTest.class,
//    ReplacementVisitorTest.class,
//    LetInlineVisitorTest.class,
//    ParameterContractionVisitorTest.class,
//    FunctionSymbolFamilyTest.class,
//    TestImmutableList.class,
//    TestLabelIntroducer.class,
//    TreeTermTranslationNoetherTest.class,
////    DafnyTreeToDeclVisitorTest.class,
//    ReferenceResolutionVisitorTest.class,
//    TypeResolutionTest.class,
//    SortTest.class,
//    ProjectTest.class,
//        ProofTest.class,
//    ScriptParserTest.class,
//        ProjectManagerTest.class,
//    ProgramDatabaseTest.class,
//    UtilTest.class,
//    DafnyRuleTest.class,
//    GenericRuleTest.class,
//    SimplifiedUpdateSequenterTest.class,
//    UpdateSequenterTest.class,
//    ParallelUpdateSequenterTest.class,
//    InlineSequenterTest.class,
//    PrettyPrintTest.class,
//    TermReferencesBuilderTest.class,
//    IntegrationTest1.class,
//    LetSubstitutionRuleTest.class,
//    TermMatcherTest.class,
//    ChainedRelationsVisitorTest.class,
//    ImplicitlyTypedVariableVisitorTest.class,
//        RuleUtilTest.class,
     
   Z3AccessTest.class, 
        SetTest.class,
         SumAndMaxTest.class,
         ClassTest.class,
        IntegerTest.class,
        FolTest.class,
        Arr1Test.class,
//        Arr2Test.class,
        SeqTest.class,
        SMTTest.class
//        
//=======
//    ParserTest.class,
//    ParserErrorTest.class,
//    SymbexTest.class,
//    ProgramDatabaseTest.class,
//    TreeTermTranslatorTest.class,
//    TreeAssignmentTranslatorTest.class,
//    ReplacementVisitorTest.class,
//    LetInlineVisitorTest.class,
//    ParameterContractionVisitorTest.class,
//    FunctionSymbolFamilyTest.class,
//    TestImmutableList.class,
//    TestLabelIntroducer.class,
//    TreeTermTranslationNoetherTest.class,
////    DafnyTreeToDeclVisitorTest.class,
//    ReferenceResolutionVisitorTest.class,
//    TypeResolutionTest.class,
//    SortTest.class,
//    ProjectTest.class,
//        ProofTest.class,
//    ScriptParserTest.class,
//        ProjectManagerTest.class,
//    ProgramDatabaseTest.class,
//    UtilTest.class,
//    DafnyRuleTest.class,
//    GenericRuleTest.class,
//    SimplifiedUpdateSequenterTest.class,
//    UpdateSequenterTest.class,
//    ParallelUpdateSequenterTest.class,
//    InlineSequenterTest.class,
//    PrettyPrintTest.class,
//    TermReferencesBuilderTest.class,
//    IntegrationTest1.class,
//    LetSubstitutionRuleTest.class,
//    TermMatcherTest.class,
//    ChainedRelationsVisitorTest.class,
//    ImplicitlyTypedVariableVisitorTest.class,
//    QuantifierGuardRemovalVisitorTest.class,
//        RuleUtilTest.class
//>>>>>>> master
    })
public class Tests {
}
