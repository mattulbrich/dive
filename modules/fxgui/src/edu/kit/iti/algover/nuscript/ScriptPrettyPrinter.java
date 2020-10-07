package edu.kit.iti.algover.nuscript;

import edu.kit.iti.algover.nuscript.ast.ScriptAST.Case;
import edu.kit.iti.algover.nuscript.ast.ScriptAST.Cases;
import edu.kit.iti.algover.nuscript.ast.ScriptAST.Command;
import edu.kit.iti.algover.nuscript.ast.ScriptAST.Parameter;
import edu.kit.iti.algover.nuscript.ast.ScriptAST.Script;
import edu.kit.iti.algover.nuscript.ast.ScriptAST.Statement;
import edu.kit.iti.algover.util.Util;

import java.util.List;

public class ScriptPrettyPrinter {

    public static CharSequence print(Script script) {
        return print(script.getStatements());
    }

    public static CharSequence print(List<Statement> stmts) {
        StringBuilder sb = new StringBuilder();
        print(sb, stmts, 0);
        return sb;
    }

    private static void print(StringBuilder sb, List<Statement> stmts, int indent) {
        for (Statement stmt : stmts) {
            print(sb, stmt, indent);
        }
    }

    private static void print(StringBuilder sb, Statement stmt, int indent) {
        stmt.visit(x -> printCommand(sb, x, indent), x -> printCases(sb, x, indent));
    }

    private static Void printCases(StringBuilder sb, Cases x, int indent) {
        sb.append(Util.duplicate(" ", indent));
        sb.append("cases {\n");

        for (Case aCase : x.getCases()) {
            sb.append(Util.duplicate(" ", indent + 2));
            sb.append("case ").append(aCase.getLabel().getText()).append(":\n");
            print(sb, aCase.getStatements(), indent + 4);
        }

        sb.append(Util.duplicate(" ", indent));
        sb.append("}\n");

        return null;
    }

    private static Void printCommand(StringBuilder sb, Command cmd, int indent) {
        sb.append(Util.duplicate("  ", indent));
        sb.append(cmd.getCommand().getText());
        for (Parameter parameter : cmd.getParameters()) {
            sb.append(" ").append(parameter.getName().getText()).append("=").append(parameter.getValue());
        }
        sb.append(";\n");
        return null;
    }
}
