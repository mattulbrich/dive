/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover;

import edu.kit.iti.algover.util.SubSelection;
import org.junit.Test;
import org.reactfx.util.Either;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

public class SubSelectionTest {

    private final SubSelection<Either<Integer, Integer>> topSelection = new SubSelection<>(s -> System.out.println(" => toplevel selection: " + s));
    private final SubSelection<Integer> leftSelection = topSelection.subSelection(SubSelectionTest::getLeftOrNull, Either::left);
    private final SubSelection<Integer> rightSelection = topSelection.subSelection(SubSelectionTest::getRightOrNull, Either::right);

    private static <A, B> A getLeftOrNull(Either<A, B> either) {
        return either.asLeft().orElse(null);
    }

    private static <A, B> B getRightOrNull(Either<A, B> either) {
        return either.asRight().orElse(null);
    }


    @Test
    public void testSubselection() {
        invariants();
        assertEquals("Initial selection is null", null, topSelection.selected().get());

        System.out.println("leftSelection.select(5)");
        leftSelection.select(5);
        invariants();
        assertEquals("Left selection updated to 5", (Integer) 5, leftSelection.selected().get());
        assertEquals("Right selection stays at null", null, rightSelection.selected().get());

        System.out.println("rightSelection.select(10)");
        rightSelection.select(10);
        invariants();
        assertEquals("Right selection updated to 10", (Integer) 10, rightSelection.selected().get());
        assertEquals("Left selection reset to null", null, leftSelection.selected().get());

        System.out.println("rightSelection.unsetGlobally()");
        rightSelection.unsetGobally();
        invariants();
        assertEquals("Unsetting the right selection sets it to null", null, rightSelection.selected().get());
        assertEquals("Unsetting the right selection sets global selection to null", null, topSelection.selected().get());
        assertEquals("Unsetting the right selection leaves left selection at null", null, leftSelection.selected().get());

        System.out.println("rightSelection.select(1)");
        rightSelection.select(1);
        invariants();
        System.out.println("leftSelection.unsetGlobally()");
        leftSelection.unsetGobally();
        invariants();
        assertEquals("Unsetting the left selection, that is already null resets the gobal selection to null", null, topSelection.selected().get());
        assertEquals("Unsetting the left selection, that is already null resets the right selection to null", null, rightSelection.selected().get());
        assertEquals("Unsetting the left selection, that is already null leaves it at null", null, leftSelection.selected().get());

        System.out.println("topSelection.select(Either.left(42))");
        topSelection.select(Either.left(42));
        invariants();
        assertEquals("Setting the top level selection to left sets the left selection", (Integer) 42, leftSelection.selected().get());
        assertEquals("Setting the top level selection to left unsets the right selection", null, rightSelection.selected().get());
    }

    private void invariants() {
        assertTrue("Invariant: Either the left or the right selection is null",
                leftSelection.selected().get() == null || rightSelection.selected().get() == null);

        if (leftSelection.selected().get() != null) {
            assertEquals("Invariant: The wrapped parts (left case) equal the top level selection",
                    Either.left(leftSelection.selected().get()),
                    topSelection.selected().get()
            );
        } else if (rightSelection.selected().get() != null) {
            assertEquals("Invariant: The wrapped parts (right case) equal the top level selection",
                    Either.right(rightSelection.selected().get()),
                    topSelection.selected().get()
            );
        } else {
            assertEquals("Invariant: The wrapped parts equal the top level selection. If both are null, the top level selection must be null",
                    null,
                    topSelection.selected().get()
            );
        }
    }
}
