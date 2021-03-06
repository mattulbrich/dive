/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.references;

import edu.kit.iti.algover.proof.Proof;
import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.rules.RuleException;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.term.prettyprint.PrettyPrint;

import java.io.IOException;
import java.nio.file.FileSystems;
import java.nio.file.Files;
import java.nio.file.Path;

public class ReferencePrettyPrinter implements ReferenceTargetVisitor<String> {

    private final Proof proof;
    private final int charWidth;
    private final PrettyPrint prettyPrinter = new PrettyPrint();

    public ReferencePrettyPrinter(Proof proof, int charWidth) {
        this.proof = proof;
        this.charWidth = charWidth;
    }

    @Override
    public String visit(CodeReferenceTarget codeTarget) {
        try {
           // String codeString = fileToString(codeTarget.getFile().getRepresentation().getFilename());
            String codeString = fileToString(codeTarget.getFile());
            String[] lines = codeString.split("\n");
            int startLine = codeTarget.getStartToken().getLine();
            int startChar = codeTarget.getStartToken().getCharPositionInLine();
            int endLine = codeTarget.getEndToken().getLine();
            int endChar = codeTarget.getEndToken().getCharPositionInLine() + codeTarget.getEndToken().getText().length();

            StringBuilder builder = new StringBuilder();
            for (int i = startLine; i <= endLine; i++) {
                String line = lines[i - 1]; // 1-based index...... ...
                if (i == startLine && i == endLine) {
                    builder.append(line.substring(startChar, endChar));
                } else if (i == startLine) {
                    builder.append(line.substring(startChar));
                } else if (i == endLine) {
                    builder.append(line.substring(0, endChar));
                } else {
                    builder.append(lines[i]);
                }
                builder.append('\n');
            }
            if (startLine == endLine) {
                return "CodeReference: " + builder.toString();
            } else {
                return "CodeReference:\n" + builder.toString();
            }
        } catch (IOException e) {
            return "<invalid reference (IOException): " + codeTarget + ">";
        }
    }

    @Override
    public String visit(ProofTermReferenceTarget termTarget) {
        try {
            ProofNode node = termTarget.getProofNodeSelector().get(proof);
            Term term = termTarget.getTermSelector().selectSubterm(node.getSequent());
            return "ProofTermReference:\n" + prettyPrinter.print(term, charWidth).toString();
        } catch (RuleException e) {
            return "<invalid reference: " + termTarget + ">";
        }
    }

    @Override
    public String visit(UserInputReferenceTarget userInputTarget) {
        return userInputTarget.toString();
    }

    @Override
    public String visit(ScriptReferenceTarget scriptTarget) {
        return scriptTarget.toString();
    }


    private static String fileToString(String filename) throws IOException {
        Path path = FileSystems.getDefault().getPath(filename);
        return new String(Files.readAllBytes(path));
    }
}
