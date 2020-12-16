/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.rule.script;

import edu.kit.iti.algover.nuscript.DefaultScriptASTVisitor;
import edu.kit.iti.algover.nuscript.Position;
import edu.kit.iti.algover.nuscript.ScriptAST;
import edu.kit.iti.algover.nuscript.ScriptAST.Case;
import edu.kit.iti.algover.nuscript.ScriptAST.Cases;
import edu.kit.iti.algover.nuscript.ScriptAST.Command;
import edu.kit.iti.algover.nuscript.ScriptAST.Statement;
import edu.kit.iti.algover.proof.Proof;
import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.proof.ProofNodeSelector;
import org.antlr.v4.runtime.Token;

import java.util.ArrayList;
import java.util.List;

public class ProofNodeCheckpointsBuilder extends DefaultScriptASTVisitor<Void, Void, RuntimeException> {
    private final Proof proof;
    private List<ProofNodeCheckpoint> checkpoints;

    public ProofNodeCheckpointsBuilder(Proof proof) {
        this.proof = proof;
    }

    public static List<ProofNodeCheckpoint> build(Proof proof) {
        ProofNodeCheckpointsBuilder builder = new ProofNodeCheckpointsBuilder(proof);
        if (proof.getProofScript() == null) {
            // hacky bugfix if the proof does not have an ast. SHould be ensured outside.
            return List.of();
        }
        builder.collectCheckpoints();
        if(builder.getCheckpoints().isEmpty()) {
            builder.getCheckpoints().add(new ProofNodeCheckpoint(new ProofNodeSelector(),
                    new Position(1,0), new Position(1,0)));
        }
        return builder.getCheckpoints();
    }

    public void collectCheckpoints() {
        this.checkpoints = new ArrayList<>();
        collectCheckpoints(proof.getProofScript().getStatements());
    }

    private void collectCheckpoints(List<Statement> statements) {

        for (Statement statement : statements) {
            statement.accept(this, null);
        }
    }

    @Override
    public Void visitCases(Cases cases, Void arg) {
        for (Case aCase : cases.getCases()) {
            List<Statement> stms = aCase.getStatements();
            if (stms.isEmpty()) {
                checkpoints.add(endOf(aCase, aCase.getProofNode()));
            } else {
                collectCheckpoints(stms);
            }
        }
        return null;
    }

    @Override
    public Void visitCommand(Command command, Void arg) throws RuntimeException {
        ProofNode node = command.getProofNode();
        if(node.getChildren() == null) {
            // If the execution failed, ...
            checkpoints.add(beginOf(command, node));
            return null;
        }

        checkpoints.add(beginOf(command, node));

        if (node.getChildren().size() > 1) {
            // ONLY IN SWING checkpoints.add(ProofNodeCheckpoint.endOf(command, node, Type.BRANCH));
        } else {

            // since we know that this rule has been applied, we definitely know that
            // there is a continuation node recording the command!
            ProofNode continuation = node.getChildren().get(0);

            assert continuation.getCommand() == command;

            List<ProofNode> children = continuation.getChildren();

            if (children == null) {
                checkpoints.add(endOf(command, continuation));
            } else if (children.isEmpty()) {
                // ONLY IN SWING checkpoints.add(ProofNodeCheckpoint.endOf(command, node, Type.CLOSED));
            }
        }

        return null;
    }

    public List<ProofNodeCheckpoint> getCheckpoints() {
        return checkpoints;
    }

    public boolean canCollect() {
        return proof.getProofScript() != null;
    }


    static ProofNodeCheckpoint endOf(ScriptAST cmd, ProofNode node) {
        Token token = cmd.getEndToken();
        Position pos = new Position(token.getLine(),
                token.getCharPositionInLine() + token.getText().length());
        return new ProofNodeCheckpoint(new ProofNodeSelector(node), pos, pos);
    }

    static ProofNodeCheckpoint beginOf(ScriptAST cmd, ProofNode node) {
        Token token = cmd.getBeginToken();
        Position pos = Position.from(token);
        return new ProofNodeCheckpoint(new ProofNodeSelector(node), pos, pos);
    }
}


//public class ProofNodeCheckpointsBuilder {
//
//    public static List<ProofNodeCheckpoint> build(Proof proof) {
//
//    }
//}
//
//        List<ProofNodeCheckpoint> result = new ArrayList<>();
//        ProofNode node = proof.getProofRoot();
//        ProofNodeSelector pns = new ProofNodeSelector();
//        collect(node, pns, result);
//        result.add(0, new ProofNodeCheckpoint(pns, new Position(0, 0), new Position(0, 0)));
//
//    @Override
//    @SuppressWarnings("unchecked") // REVIEW: Repair this as soon as the scripts are correctly generically treated
//    public Void visit(SimpleCaseStatement simpleCaseStatement) {
//        int selectedChildIdx = -1;
//        for (int i = 0; lastHandledNodes.size() > 0 && i < lastHandledNodes.get(inCase - 1).getChildren().size(); ++i) {
//            //TODO only label matching no sequent matching supported as of yet
//            if(simpleCaseStatement.getGuard() instanceof MatchExpression) {
//                if (simpleCaseStatement.getGuard().getText().
//                        substring(6, simpleCaseStatement.getGuard().getText().length() - 1).
//                        equals(lastHandledNodes.get(inCase - 1).getChildren().get(i).getLabel())) {
//                    selectedChildIdx = i;
//                }
//            } else if(simpleCaseStatement.getGuard() instanceof StringLiteral) {
//                if (simpleCaseStatement.getGuard().getText().
//                        substring(1, simpleCaseStatement.getGuard().getText().length() - 1).
//                        equals(lastHandledNodes.get(inCase - 1).getChildren().get(i).getLabel())) {
//                    selectedChildIdx = i;
//                }
//            } else {
//                throw new UnsupportedOperationException("Only string labels for case matches supported.");
//            }
//
//        }
//        if (selectedChildIdx != -1) {
//            ProofNodeSelector selector = new ProofNodeSelector(lastHandledSelectors.get(inCase - 1), selectedChildIdx);
//            Position position = simpleCaseStatement.getStartPosition();
//            Position guardPosition = simpleCaseStatement.getGuard().getEndPosition();
//            Position caretPosition = new Position(position.getLineNumber() + 1, 2);
//            checkpoints.add(new ProofNodeCheckpoint(selector, position, caretPosition));
//        }
//        // TODO: Find out how to get a ProofNodeSelector out of a specific case (rudimentary solution above)
//        // (so that you can click inside an empty case to see what it's sequent state looks like)
//        // (same for the CaseStatement visit)
//        simpleCaseStatement.getBody().forEach(statement -> statement.accept(this));
//        return null;
//    }
//
//    private static void collect(ProofNode node, ProofNodeSelector pns, List<ProofNodeCheckpoint> result) {
//        Command command = node.getCommand();
//        if (command != null) {
//            Position pos = command.getPosition();
//            result.add(new ProofNodeCheckpoint(pns, pos, pos));
//        }
//        int number = 0;
//        for (ProofNode child : node.getSuccessors()) {
//            ProofNodeSelector childPNS = new ProofNodeSelector(pns, number);
//            collect(child, pns, result);
//            number++;
//        }
//    }
//}
//    private final List<ProofNodeCheckpoint> checkpoints;
//    private final ProofNode rootProofNode;
//    private List<ProofNode> lastHandledNodes;
//    private List<ProofNodeSelector> lastHandledSelectors;
//    private int inCase = 0;
//
//    private ProofNodeCheckpointsBuilder(ProofNode rootProofNode) {
//        this.rootProofNode = rootProofNode;
//        lastHandledNodes = new ArrayList<>(Collections.singletonList(rootProofNode));
//        lastHandledSelectors = new ArrayList<>(Collections.singletonList(new ProofNodeSelector()));
//        checkpoints = new ArrayList<>();
//        checkpoints.add(new ProofNodeCheckpoint(new ProofNodeSelector(), new Position(0, 0), new Position(1, 0)));
//    }
//
//    public static List<ProofNodeCheckpoint> build(ProofNode root, ProofScript script) {
//        ProofNodeCheckpointsBuilder builder = new ProofNodeCheckpointsBuilder(root);
//        if (script == null) {
//            return builder.checkpoints;
//        }
//        script.accept(builder);
//        return builder.checkpoints;
//    }
//
//    @Override
//    public Void visit(ProofScript proofScript) {
//        return proofScript.getBody().accept(this);
//    }
//
//    @Override
//    @SuppressWarnings("unchecked") // REVIEW: Repair this as soon as the scripts are correctly generically treated
//    public Void visit(Statements statements) {
//        statements.forEach(node -> node.accept(this));
//        return null;
//    }
//
//    @Override
//    public Void visit(CallStatement call) {
//        ProofNodeSelector selectorBefore = findSelectorPointingTo(new ProofNodeSelector(), rootProofNode, call);
//        if (selectorBefore != null) {
//            ProofNodeSelector selector = new ProofNodeSelector(selectorBefore, 0);
//            Position position = call.getEndPosition();
//            try {
//                if(inCase > lastHandledNodes.size() - 1) {
//                    lastHandledNodes.add(selectorBefore.getNode(rootProofNode));
//                    lastHandledSelectors.add(selectorBefore);
//                } else {
//                    lastHandledNodes.set(inCase, selectorBefore.getNode(rootProofNode));
//                    lastHandledSelectors.set(inCase, selectorBefore);
//                }
//            } catch (RuleException ex) {
//                System.out.println("Could not select last handled node.");
//            }
//            checkpoints.add(new ProofNodeCheckpoint(selector, position, new Position(position.getLineNumber() + 1, 0)));
//        }
//        return null;
//    }
//
//    @Override
//    public Void visit(CasesStatement cases) {
//        inCase++;
//        cases.getCases().forEach(caze -> caze.accept(this));
//        inCase--;
//        return null;
//    }
//
//    @Override
//    @SuppressWarnings("unchecked") // REVIEW: Repair this as soon as the scripts are correctly generically treated
//    public Void visit(SimpleCaseStatement simpleCaseStatement) {
//        int selectedChildIdx = -1;
//        for (int i = 0; lastHandledNodes.size() > 0 && i < lastHandledNodes.get(inCase - 1).getChildren().size(); ++i) {
//            //TODO only label matching no sequent matching supported as of yet
//            if (simpleCaseStatement.getGuard().getText().
//                    substring(6, simpleCaseStatement.getGuard().getText().length() - 1).
//                    equals(lastHandledNodes.get(inCase - 1).getChildren().get(i).getLabel())) {
//                selectedChildIdx = i;
//            }
//        }
//        if (selectedChildIdx != -1) {
//            ProofNodeSelector selector = new ProofNodeSelector(lastHandledSelectors.get(inCase - 1), selectedChildIdx);
//            Position position = simpleCaseStatement.getStartPosition();
//            Position guardPosition = simpleCaseStatement.getGuard().getEndPosition();
//            Position caretPosition = new Position(position.getLineNumber() + 1, 2);
//            checkpoints.add(new ProofNodeCheckpoint(selector, position, caretPosition));
//        }
//        // TODO: Find out how to get a ProofNodeSelector out of a specific case (rudimentary solution above)
//        // (so that you can click inside an empty case to see what it's sequent state looks like)
//        // (same for the CaseStatement visit)
//        simpleCaseStatement.getBody().forEach(statement -> statement.accept(this));
//        return null;
//    }
//
//    @Override
//    public Void visit(CaseStatement caseStatement) {
//        caseStatement.getBody().accept(this);
//        return null;
//    }
//
//    // REVIEW: Repair this as soon as the proof script generics have been done
//    @SuppressWarnings({"unchecked", "rawtypes"})
//    private ProofNodeSelector findSelectorPointingTo(ProofNodeSelector pathSoFar, ProofNode proofNode, ASTNode node) {
//        if (rlyContains((List)proofNode.getMutator(), node)) {
//            return pathSoFar;
//        } else {
//            for (int i = 0; i < proofNode.getChildren().size(); i++) {
//                ProofNode child = proofNode.getChildren().get(i);
//                ProofNodeSelector subselector = findSelectorPointingTo(new ProofNodeSelector(pathSoFar, i), child, node);
//                if (subselector != null) {
//                    return subselector;
//                }
//            }
//            return null;
//        }
//    }
//
//    private  boolean rlyContains(List<ASTNode> l, ASTNode n) {
//        for(ASTNode n1 : l) {
//            if(n == n1) return true;
//        }
//        return false;
//    }
//
//}
