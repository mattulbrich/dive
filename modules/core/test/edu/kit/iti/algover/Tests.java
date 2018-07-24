/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover;


import org.junit.runner.RunWith;
import org.junit.runners.Suite;
import org.junit.runners.Suite.SuiteClasses;

import edu.kit.iti.algover.rules.impl.Z3RuleTest;
import edu.kit.iti.algover.smttrans.translate.Arr1Test;
import edu.kit.iti.algover.smttrans.translate.Arr1UnitTest;
import edu.kit.iti.algover.smttrans.translate.Arr2UnitTest;
import edu.kit.iti.algover.smttrans.translate.ClassTest;
import edu.kit.iti.algover.smttrans.translate.DafnyExampleTest;
import edu.kit.iti.algover.smttrans.translate.FolTest;
import edu.kit.iti.algover.smttrans.translate.IntegerTest;
import edu.kit.iti.algover.smttrans.translate.MultisetUnitTest;
import edu.kit.iti.algover.smttrans.translate.ObjectUnitTest;
import edu.kit.iti.algover.smttrans.translate.SeqUnitTest;
import edu.kit.iti.algover.smttrans.translate.SetUnitTest;
import edu.kit.iti.algover.smttrans.translate.SumAndMaxTest;

@RunWith(Suite.class)
@SuiteClasses({



        DafnyExampleTest.class,
   //     Arr1Test.class,
    //    ClassTest.class,
     //   FolTest.class,
    //    SumAndMaxTest.class,
   //     IntegerTest.class,
   // SetUnitTest.class,
  //  Arr2UnitTest.class,
  //  SeqUnitTest.class,
 //   MultisetUnitTest.class,
// 
//    Arr1UnitTest.class
    
   //    ObjectUnitTest.class
   //     Z3RuleTest.class
    

    })
public class Tests {
}
