/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.script.interpreter;

import edu.kit.iti.algover.data.SymbolTable;
import edu.kit.iti.algover.parser.DafnyException;
import edu.kit.iti.algover.parser.DafnyParserException;
import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.script.ast.Signature;
import edu.kit.iti.algover.script.ast.Type;
import edu.kit.iti.algover.script.data.Value;
import edu.kit.iti.algover.script.data.VariableAssignment;
import edu.kit.iti.algover.term.Sequent;
import edu.kit.iti.algover.term.match.SequentMatcher;
import edu.kit.iti.algover.term.parser.TermParser;

import java.util.ArrayList;
import java.util.List;
import java.util.regex.MatchResult;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

/**
 * MatcherApi for Sequents, Terms and Labels
 */
public class TermMatcherApi<T> implements MatcherApi<T> {
    private List<MatchResult> resultsFromLabelMatch;

    /**
     * Match a branch label
     * @param currentState
     * @param label
     * @return
     */
    @Override
    public List<VariableAssignment> matchLabel(ProofNode currentState, String label) {

        List<VariableAssignment> assignments = new ArrayList<>();
        resultsFromLabelMatch = new ArrayList<>();
        //compile pattern
        String cleanLabel = cleanLabel(label);
        //String cleanLabel = label;

        String branchLabel = currentState.getLabel();
        String cleanBranchLabel = branchLabel.replaceAll(" ", "");
        //cleanLabel(branchLabel);


        Pattern regexpForLabel = Pattern.compile("\\\\Q" + cleanLabel + "\\\\E");
        Matcher branchLabelMatcher = regexpForLabel.matcher(Pattern.quote(cleanBranchLabel));

        //Matcher branchLabelMatcher = regexpForLabel.matcher(cleanBranchLabel);


        if (branchLabelMatcher.matches()) {
            VariableAssignment va = new VariableAssignment(null);
            va.declare("$$Label_", Type.STRING);
            va.assign("$$Label_", Value.from(branchLabelMatcher.group()));
            assignments.add(va);
            resultsFromLabelMatch.add(branchLabelMatcher.toMatchResult());
        }


        // assignments.forEach(variableAssignment -> System.out.println(variableAssignment));
        return assignments.isEmpty() ? null : assignments;
    }

    /**
     * Match a schema sequent. At the moment no really used
     * @param currentState
     * @param data
     * @param sig
     * @return
     */
    @Override
    public List<VariableAssignment> matchSeq(ProofNode currentState, String data, Signature sig) {
        SequentMatcher matcher = new SequentMatcher();
        SymbolTable symbTable = currentState.getAllSymbols();
        TermParser tp = new TermParser(symbTable);
        tp.setSchemaMode(true);
        try {
            Sequent pattern = tp.parseSequent(data);
            matcher.match(pattern, currentState.getSequent());
        } catch (DafnyParserException e) {
            e.printStackTrace();
        } catch (DafnyException e) {
            e.printStackTrace();
        }
        // return matcher.match(currentState.getSequent(),);
        return null;
    }

    /**
     * Clean special symbols from label
     * @param label
     * @return
     */
    private static String cleanLabel(String label) {

        String cleaned = label.replaceAll(" ", "");
        cleaned = cleaned.replaceAll("\\(", "\\\\(");
        cleaned = cleaned.replaceAll("\\)", "\\\\)");
        cleaned = cleaned.replaceAll("\\[", "\\\\[");
        cleaned = cleaned.replaceAll("\\]", "\\\\]");

        return cleaned;
    }

}
