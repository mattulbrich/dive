/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.util;

import de.uka.ilkd.pp.NoExceptions;
import edu.kit.iti.algover.proof.PVCCollection;
import edu.kit.iti.algover.proof.ProofFormula;
import edu.kit.iti.algover.term.ApplTerm;
import edu.kit.iti.algover.term.FunctionSymbol;
import edu.kit.iti.algover.term.LetTerm;
import edu.kit.iti.algover.term.QuantTerm;
import edu.kit.iti.algover.term.SchemaCaptureTerm;
import edu.kit.iti.algover.term.SchemaOccurTerm;
import edu.kit.iti.algover.term.SchemaTerm;
import edu.kit.iti.algover.term.SchemaVarTerm;
import edu.kit.iti.algover.term.Sequent;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.term.TermVisitor;
import edu.kit.iti.algover.term.VariableTerm;

import java.io.PrintStream;

public class Debug {


    public static CharSequence prettyPrint(CharSequence cs) {

        int len = cs.length();
        int level = 0;
        StringBuilder sb = new StringBuilder();
        for (int i = 0; i < len; i++) {

            char c = cs.charAt(i);
            switch(c) {
            case '(':
                level++;
                sb.append("\n").append(Util.duplicate(" ", level));
                break;
            case ')':
                level--;
                break;
            }
            sb.append(c);
        }

        return sb;

    }

    public static CharSequence toString(PVCCollection coll)  {
        StringBuilder sb = new StringBuilder();
        toString(sb, coll, 0);
        return sb;
    }

    private static void toString(StringBuilder sb, PVCCollection coll, int indent) {
        sb.append(Util.duplicate("   ", indent))
            .append(coll.toString())
            .append("\n");
        for (PVCCollection child : coll.getChildren()) {
            toString(sb, child, indent + 1);
        }
    }

    public static void dumpSeq(Sequent sequent) {
        dumpSeq(System.err, sequent);
    }

    public static void dumpSeq(PrintStream ps, Sequent seq) {
        ps.println("<seq>");
        ps.println("  <ante>");
        for (ProofFormula formula : seq.getAntecedent()) {
            dumpTerm(ps, formula.getTerm(), 4);
        }
        ps.println("  </ante>");
        ps.println("  <succ>");
        for (ProofFormula formula : seq.getSuccedent()) {
            dumpTerm(ps, formula.getTerm(), 4);
        }
        ps.println("  </succ>");
        ps.println("</seq>");

    }

    public static void dumpTerm(Term term) {
        dumpTerm(System.err, term, 0);
    }

    private static void dumpTerm(PrintStream ps, Term term, int indent) {
        term.accept(new TermVisitor<Integer, Void, NoExceptions>() {
            @Override
            public Void visit(VariableTerm variableTerm, Integer indent) throws NoExceptions {
                ps.print(Util.duplicate(" ", indent));
                ps.println("<var sort=\"" + variableTerm.getSort() + "\">" +
                        variableTerm.getName() + "</var>");
                return null;
            }

            @Override
            public Void visit(QuantTerm quantTerm, Integer indent) throws NoExceptions {
                ps.print(Util.duplicate(" ", indent));
                VariableTerm boundVar = quantTerm.getBoundVar();
                ps.printf("<quant q=\"%s\" var=\"%s\" sort=\"%s\">%n",
                        quantTerm.getQuantifier(), boundVar.getName(), boundVar.getSort());
                quantTerm.getTerm(0).accept(this, indent + 2);
                ps.print(Util.duplicate(" ", indent));
                ps.println("</quant>");
                return null;
            }

            @Override
            public Void visit(ApplTerm app, Integer indent) throws NoExceptions {
                ps.print(Util.duplicate(" ", indent));
                FunctionSymbol fs = app.getFunctionSymbol();
                ps.printf("<app fs=\"%s\" hash=\"%d\">%n",
                        fs.getName(), fs.hashCode());
                for (Term subterm : app.getSubterms()) {
                    subterm.accept(this, indent + 2);
                }
                ps.print(Util.duplicate(" ", indent));
                ps.println("</app>");
                return null;
            }

            @Override
            public Void visit(LetTerm letTerm, Integer indent) throws NoExceptions {
                ps.print(Util.duplicate(" ", indent));
                ps.println("<let>");
                for (Pair<VariableTerm, Term> subst : letTerm.getSubstitutions()) {
                    ps.print(Util.duplicate(" ", indent + 2));
                    ps.println("<subst var=\"" + subst.getFst().getName() + "\">");
                    subst.snd.accept(this, indent + 2);
                    ps.print(Util.duplicate(" ", indent + 2));
                    ps.println("</subst>");
                }
                letTerm.getTerm(0).accept(this, indent + 2);
                ps.print(Util.duplicate(" ", indent));
                ps.println("</app>");
                return null;
            }

            @Override
            public Void visit(SchemaOccurTerm occurTerm, Integer indent) throws NoExceptions {
                ps.print(Util.duplicate(" ", indent));
                ps.println("<occur>");
                occurTerm.getTerm(0).accept(this, indent + 2);
                ps.print(Util.duplicate(" ", indent));
                ps.println("</occur>");
                return null;
            }

            @Override
            public Void visit(SchemaVarTerm schemaVarTerm, Integer indent) throws NoExceptions {
                ps.print(Util.duplicate(" ", indent));
                ps.println("<schemavar sort=\"" + schemaVarTerm.getSort() + "\">" +
                        schemaVarTerm.getName() + "</schemavar>");
                return null;
            }

            @Override
            public Void visit(SchemaCaptureTerm cap, Integer indent) throws NoExceptions {
                ps.print(Util.duplicate(" ", indent));
                ps.println("<schemacap sort=\"" + cap.getSort() + "\">" + cap.getName());
                cap.getTerm(0).accept(this, indent + 2);
                ps.print(Util.duplicate(" ", indent));
                ps.println("</schemacap>");
                return null;
            }
        }, indent);
    }
}
