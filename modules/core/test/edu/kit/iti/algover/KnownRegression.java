/*
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2020 Karlsruhe Institute of Technology
 */

package edu.kit.iti.algover;

/**
 * This is a marker interface to mark test cases which are known to fail.
 * The fact is acknowledged and should be fixed soon.
 * Ideally there should be an accompanying issue in the bugtracker which
 * should be mentioned in a comment near the test case.
 *
 * Known regressions make the build "yellow" but not "red".
 */
public interface KnownRegression {
    // deliberately empty
}