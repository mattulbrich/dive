package edu.kit.iti.algover.nuscript;

import edu.kit.iti.algover.nuscript.ScriptAST.ByClause;
import edu.kit.iti.algover.nuscript.ScriptAST.Case;
import edu.kit.iti.algover.nuscript.ScriptAST.Cases;
import edu.kit.iti.algover.nuscript.ScriptAST.Command;
import edu.kit.iti.algover.nuscript.ScriptAST.Parameter;
import edu.kit.iti.algover.nuscript.ScriptAST.Script;
import edu.kit.iti.algover.nuscript.ScriptAST.Statement;
import edu.kit.iti.algover.nuscript.parser.Scripts;
import org.junit.Test;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNull;

public class ParentRelationVisitorTest {

    private static final String testScript = "cmd by { c1; c2; } cmd;" +
            " cases { \"case 1\": cmd; cmd by otherCmd; \"case 2\": skip; \"opencase\": }";

    @Test
    public void testParentRelation() throws Exception {
        Script script = Scripts.parseScript(testScript);
        ParentRelationVisitor.setParentRelation(script);
        script.accept(new ParentCheck(), null);
    }

    private static class ParentCheck implements ScriptASTVisitor<ScriptAST, Void, RuntimeException> {

        @Override
        public Void visitScript(Script script, ScriptAST arg) throws RuntimeException {
            assertNull(script.getParent());
            for (Statement statement : script.getStatements()) {
                statement.accept(this, script);
            }
            return null;
        }

        @Override
        public Void visitCommand(Command command, ScriptAST arg) throws RuntimeException {
            assertEquals(arg, command.getParent());
            for (Parameter parameter : command.getParameters()) {
                parameter.accept(this, command);
            }
            if(command.getByClause() != null) {
                command.getByClause().accept(this, command);
            }
            return null;
        }

        @Override
        public Void visitParameter(Parameter parameter, ScriptAST arg) throws RuntimeException {
            assertEquals(arg, parameter.getParent());
            return null;
        }

        @Override
        public Void visitCases(Cases cases, ScriptAST arg) throws RuntimeException {
            assertEquals(arg, cases.getParent());
            for (Case aCase : cases.getCases()) {
                aCase.accept(this, cases);
            }
            return null;
        }

        @Override
        public Void visitCase(Case aCase, ScriptAST arg) throws RuntimeException {
            assertEquals(arg, aCase.getParent());
            for (Statement statement : aCase.getStatements()) {
                statement.accept(this, aCase);
            }
            return null;
        }

        @Override
        public Void visitByClause(ByClause byClause, ScriptAST arg) throws RuntimeException {
            assertEquals(arg, byClause.getParent());
            return null;
        }
    }

}