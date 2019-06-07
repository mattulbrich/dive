/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.util;

import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;

/**
 * This java annotation is purely for documentation purposes. It has no
 * meaning.
 *
 * All methods/classes/fields which are important to build up test cases should
 * be tagged with this annotation.
 *
 * Using "grep" or "Find usages" from within an IDE, this facilitates finding out
 * how to mock entities or achieve goals in algover tests.
 *
 * All annotated entities MUST have a javadoc.
 *
 * @author Mattias Ulbrich
 */

@Retention(RetentionPolicy.SOURCE)
public @interface TestInfrastructure {
}
