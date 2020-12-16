package edu.kit.iti.algover.nuscript;

import edu.kit.iti.algover.nuscript.ScriptAST.ByClause;
import edu.kit.iti.algover.nuscript.ScriptAST.Case;
import edu.kit.iti.algover.nuscript.ScriptAST.Cases;
import edu.kit.iti.algover.nuscript.ScriptAST.Command;
import edu.kit.iti.algover.nuscript.ScriptAST.Script;

/**
 * This visitor can be used to set the {@link ScriptAST#parent} fields correctly.
 *
 * It can be run once after the AST has been constructed to update all fields.
 *
 * Run it as follows:
 * <pre>
 *    Script script;
 *    // ...
 *    ParentRelationVisitor.setParentRelation(script);
 * </pre>
 *
 * This class is a singleton.
 *
 * @author Mattias Ulbrich
 */
public class ParentRelationVisitor extends DefaultScriptASTVisitor<ScriptAST, Void, RuntimeException> {

    /**
     * The singleton instance.
     */
    private static ParentRelationVisitor INSTANCE;

    /**
     * Constructor can only be used for the singleton instance.
     */
    private ParentRelationVisitor() {
        // deliberately empty.
    }

    /**
     * set all parent relations within the given AST.
     * The top-most (entry) node will be set to a null parent.
     *
     * @param ast a non-null script ast node.
     */
    public static void setParentRelation(ScriptAST ast) {
        setParentRelation(ast, null);
    }

    /**
     * set all parent relations within the given AST.
     *
     * @param ast a non-null script ast node.
     * @param parent the parent for the top-most (entry) node
     */
    private static void setParentRelation(ScriptAST ast, ScriptAST parent) {
        if(INSTANCE == null) {
            INSTANCE = new ParentRelationVisitor();
        }
        ast.accept(INSTANCE, parent);
    }

    @Override
    protected Void visitDefault(ScriptAST ast, ScriptAST arg) throws RuntimeException {
        ast.setParent(arg);
        return null;
    }

    @Override
    public Void visitScript(Script script, ScriptAST arg) throws RuntimeException {
        visitStatements(script, script);
        return visitDefault(script, arg);
    }

    @Override
    public Void visitCommand(Command command, ScriptAST arg) throws RuntimeException {
        visitCommandChildren(command, command);
        return visitDefault(command, arg);
    }

    @Override
    public Void visitCases(Cases cases, ScriptAST arg) throws RuntimeException {
        for (Case aCase : cases.getCases()) {
            aCase.accept(this, cases);
        }
        return visitDefault(cases, arg);
    }

    @Override
    public Void visitCase(Case aCase, ScriptAST arg) throws RuntimeException {
        visitStatements(aCase, aCase);
        return visitDefault(aCase, arg);
    }

    @Override
    public Void visitByClause(ByClause byClause, ScriptAST arg) throws RuntimeException {
        visitStatements(byClause, byClause);
        return visitDefault(byClause, arg);
    }
}
