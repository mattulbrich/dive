/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 *
 */

package edu.kit.iti.algover.boogie;

import org.junit.runner.RunWith;
import org.junit.runners.Suite;
import org.junit.runners.Suite.SuiteClasses;

@SuiteClasses({
        BoogieProcessTest.class,
        SetSoundnessTests.class,
        SetCompletenessTests.class,
        SeqSoundnessTest.class,
        SeqCompletenessTests.class,
        Array1SoundnessTests.class,
        Array1CompletenessTests.class,
        HeapTests.class,
})
@RunWith(Suite.class)
public class Tests {

}
