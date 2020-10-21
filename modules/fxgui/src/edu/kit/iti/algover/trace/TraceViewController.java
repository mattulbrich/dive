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

import edu.kit.iti.algover.PropertyManager;
import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.term.LetTerm;
import edu.kit.iti.algover.term.Sequent;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.term.VariableTerm;
import edu.kit.iti.algover.term.prettyprint.PrettyPrint;
import edu.kit.iti.algover.util.Pair;
import javafx.beans.value.ObservableValue;

import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.List;
import java.util.stream.Collectors;

public class TraceViewController {

    public TraceViewController() {
        PropertyManager.getInstance().currentProofNode.addListener(this::showSelectedNode);
    }

    private void showSelectedNode(ObservableValue<? extends ProofNode> observableValue, ProofNode oldValue, ProofNode newValue) {
        if(newValue != null) {
            PrettyPrint pp = new PrettyPrint();
            Sequent seq = newValue.getSequent();
            List<VariableTerm> referencedVars = new ArrayList<>();
            List<Term> succ = seq.getSuccedent().stream().map(pf -> pf.getTerm()).collect(Collectors.toList());
            for(Term t : succ) {
                referencedVars.addAll(extractReferencedVars(extractTerm(t)));
            }
            List<Term> ante = seq.getAntecedent().stream().map(pf -> pf.getTerm()).collect(Collectors.toList());
            ante.sort(Comparator.comparingInt(this::getLetDepth));
            List<Pair<VariableTerm, Term>> assignments = new ArrayList<>();
            System.out.println("\n\n");
            for (Term t : ante) {
                List<Pair<VariableTerm, Term>> newAssignments = extractAssignments(t);
                newAssignments.removeAll(assignments);
                assignments.addAll(newAssignments);
                for(Pair<VariableTerm, Term> p : newAssignments) {
                    if(referencedVars.contains(p.fst)) {
                        System.out.println("Assignment: " + pp.print(p.fst) + " = " + pp.print(p.snd));
                    }
                }
                System.out.println("Assume: " + pp.print(extractTerm(t)));
            }
            succ.sort(Comparator.comparingInt(this::getLetDepth));
            System.out.println("succ");
            for (Term t : succ) {
                List<Pair<VariableTerm, Term>> newAssignments = extractAssignments(t);
                newAssignments.removeAll(assignments);
                assignments.addAll(newAssignments);
                for(Pair<VariableTerm, Term> p : newAssignments) {
                    if(referencedVars.contains(p.fst)) {
                        System.out.println("Assignment: " + pp.print(p.fst) + " = " + pp.print(p.snd));
                    }
                }
                System.out.println("Assert: " + pp.print(extractTerm(t)));
            }
        }
    }

    private int getLetDepth(Term term) {
        if(term instanceof LetTerm) {
            return 1 + Collections.max(term.getSubterms().stream().map(t -> getLetDepth(t)).collect(Collectors.toList()));
        }
        return 0;
    }

    private Term extractTerm(Term letTerm) {
        if(letTerm.getTerm(0) instanceof LetTerm) {
            return extractTerm(letTerm.getTerm(0));
        }
        return letTerm.getTerm(0);
    }

    private List<Pair<VariableTerm, Term>> extractAssignments(Term term) {
        if(term instanceof LetTerm) {
            List<Pair<VariableTerm, Term>> assignments = new ArrayList<>();
            assignments.addAll(((LetTerm) term).getSubstitutions());
            assignments.addAll(extractAssignments(term.getTerm(0)));
            return assignments;
        }
        return new ArrayList<>();
    }

    private List<VariableTerm> extractReferencedVars(Term term) {
        List<VariableTerm> vars = new ArrayList<>();
        if(term instanceof VariableTerm) {
            vars.add((VariableTerm)term);
            return vars;
        }
        term.getSubterms().forEach(t -> vars.addAll(extractReferencedVars(t)));
        return vars;
    }

}
