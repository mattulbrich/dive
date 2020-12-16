package edu.kit.iti.algover.nuscript;

import edu.kit.iti.algover.nuscript.ScriptAST.ByClause;
import edu.kit.iti.algover.nuscript.ScriptAST.Case;
import edu.kit.iti.algover.nuscript.ScriptAST.Cases;
import edu.kit.iti.algover.nuscript.ScriptAST.Command;
import edu.kit.iti.algover.nuscript.ScriptAST.Parameter;
import edu.kit.iti.algover.nuscript.ScriptAST.Script;
import edu.kit.iti.algover.nuscript.ScriptAST.Statement;
import edu.kit.iti.algover.util.Conditional;
import edu.kit.iti.algover.util.Util;

import java.io.IOException;
import java.util.List;

/**
 * Print the AST (such that it can be parsed again) to a writer
 * @param writer a non-null object to write to
 * @param indentation the level of indentation for the spaces in the line
 * @throws IOException if writing fails
 */
public class PrintVisitor implements ScriptASTVisitor<Integer, Void, IOException> {

    private final Appendable writer;

    public PrintVisitor(Appendable writer) {
        this.writer = writer;
    }

    @Override
    public Void visitScript(Script script, Integer indentation) throws IOException {
        Conditional conditional = Conditional.notAtFirst();
        for (Statement statement : script.getStatements()) {
            conditional.run(() -> writer.append("\n"));
            statement.accept(this, indentation);
        }
        return null;
    }

    @Override
    public Void visitCommand(Command command, Integer indentation) throws IOException {
        writer.append(Util.duplicate("  ", indentation) +
                command.getCommand().getText());
        for (Parameter p : command.getParameters()) {
            writer.append(" ");
            p.accept(this, indentation);
        }
        if (command.getByClause() == null) {
            writer.append(";");
        } else {
            command.getByClause().accept(this, indentation);
        }
        return null;
    }

    @Override
    public Void visitParameter(Parameter parameter, Integer indentation) throws IOException {
        if (parameter.getName() != null) {
            writer.append(parameter.getName().getText()).append("=");
        }
        writer.append(parameter.getValue().getText());
        return null;
    }

    @Override
    public Void visitCases(Cases cases, Integer indentation) throws IOException {
        writer.append(Util.duplicate("  ", indentation)).append("cases {");
        for (Case cas : cases.getCases()) {
            writer.append("\n");
            cas.accept(this, indentation);
        }
        writer.append("\n").append(Util.duplicate("  ", indentation)).append("}");

        return null;
    }

    @Override
    public Void visitCase(Case aCase, Integer indentation) throws IOException {
        indentation ++;
        writer.append(Util.duplicate("  ", indentation)).
                append(aCase.getLabel().getText()).append(":");
        indentation ++;
        for (Statement statement : aCase.getStatements()) {
            writer.append("\n");
            statement.accept(this, indentation);
        }
        return null;
    }

    @Override
    public Void visitByClause(ByClause byClause, Integer indentation) throws IOException {
        writer.append(" by ");
        List<Statement> statements = byClause.getStatements();
        if (statements.size() == 1) {
            statements.get(0).accept(this, 0);
        } else {
            writer.append("{");
            indentation ++;
            for (Statement statement : statements) {
                writer.append("\n");
                statement.accept(this, indentation);
            }
            indentation --;
            writer.append("\n").
                    append(Util.duplicate("  ", indentation)).
                    append("}");
        }
        return null;
    }
}
