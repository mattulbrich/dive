/*
 * This file is part of DIVE.
 *
 * DIVE is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * Foobar is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with Foobar.  If not, see <https://www.gnu.org/licenses/>.
 */

package edu.kit.iti.algover.trace;

import edu.kit.iti.algover.data.BuiltinSymbols;
import edu.kit.iti.algover.rules.TermSelector;
import edu.kit.iti.algover.sequent.formulas.ViewFormula;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.term.builder.TermBuildException;
import edu.kit.iti.algover.term.builder.TermBuilder;
import edu.kit.iti.algover.util.ImmutableList;

public class ViewAssignment extends ViewFormula {
    private static Term createAssignment(Term var, Term value) {
        TermBuilder tb = new TermBuilder(new BuiltinSymbols());
        try {
            return tb.eq(var, value);
        } catch (TermBuildException e) {
            throw new RuntimeException("Error creating assignment.");
        }
    }

    public ViewAssignment(int indexInSequent, Term var, Term value) {
        super(indexInSequent, createAssignment(var, value), Type.ORIGINAL, TermSelector.SequentPolarity.ANTECEDENT, ImmutableList.single("Assignment"));
    }
}
