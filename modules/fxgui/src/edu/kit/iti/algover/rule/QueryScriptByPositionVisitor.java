package edu.kit.iti.algover.rule;

import edu.kit.iti.algover.script.ast.ASTNode;
import edu.kit.iti.algover.script.ast.Position;
import edu.kit.iti.algover.script.ast.Statement;
import edu.kit.iti.algover.script.ast.Statements;
import edu.kit.iti.algover.script.parser.DefaultASTVisitor;
import edu.kit.iti.algover.util.Span;

public class QueryScriptByPositionVisitor extends DefaultASTVisitor<ASTNode> {

    private final Position queryPosition;

    public QueryScriptByPositionVisitor(Position queryPosition) {
        this.queryPosition = queryPosition;
    }

    @Override
    public ASTNode defaultVisit(ASTNode node) {
        if (matchesQuery(node)) {
            return node;
        } else {
            return null;
        }
    }

    @Override
    public ASTNode visit(Statements statements) {
        for (Statement<?> statement : statements) {
            ASTNode foundNode = statement.accept(this);
            if (foundNode != null) {
                return foundNode;
            }
        }
        return null;
    }

    private boolean matchesQuery(ASTNode node) {
        return isBetween(node.getStartPosition(), node.getEndPosition(), queryPosition);
    }

    private static boolean isBetween(Position start, Position end, Position query) {
        return new Span(start.getLineNumber(), end.getLineNumber(), start.getCharInLine(), end.getCharInLine())
                .containsPosition(query.getLineNumber(), query.getCharInLine());
    }
}
