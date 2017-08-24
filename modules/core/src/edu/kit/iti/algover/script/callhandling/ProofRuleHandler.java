package edu.kit.iti.algover.script.callhandling;

import edu.kit.iti.algover.proof.ProofFormula;
import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.rules.*;
import edu.kit.iti.algover.script.ast.CallStatement;
import edu.kit.iti.algover.script.ast.Expression;
import edu.kit.iti.algover.script.data.GoalNode;
import edu.kit.iti.algover.script.data.State;
import edu.kit.iti.algover.script.data.Value;
import edu.kit.iti.algover.script.data.VariableAssignment;
import edu.kit.iti.algover.script.exceptions.ScriptCommandNotApplicableException;
import edu.kit.iti.algover.script.interpreter.Evaluator;
import edu.kit.iti.algover.script.interpreter.Interpreter;
import edu.kit.iti.algover.term.Sequent;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.util.ImmutableList;
import edu.kit.iti.algover.util.Pair;
import jdk.nashorn.internal.codegen.types.Type;
import sun.reflect.generics.reflectiveObjects.NotImplementedException;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

/**
 * Handler for ProofRules
 *
 * @author S. Grebing
 */
public class ProofRuleHandler implements CommandHandler<ProofNode> {
    private List<ProofRule> rules = new ArrayList<>();
    private Map<String, ProofRule> ruleMap = new HashMap<>();


    public ProofRuleHandler() {
    }

    public ProofRuleHandler(List<ProofRule> rules) {

        this.rules = rules;
        rules.forEach(proofRule -> ruleMap.put(proofRule.getName(), proofRule));
    }

    @Override
    public boolean handles(CallStatement call) throws IllegalArgumentException {
        for (ProofRule pr : rules)
            if (pr.getName().equals(call.getCommand())) {
                return true;
            }
        return false;
    }

    @Override
    public void evaluate(Interpreter<ProofNode> interpreter, CallStatement call, VariableAssignment params) throws IllegalStateException, ScriptCommandNotApplicableException {
        if (!rules.contains(call.getCommand())) {
            throw new IllegalStateException();
        }
        ProofRule pr = ruleMap.get(call.getCommand());
        State<ProofNode> state = interpreter.getCurrentState();
        GoalNode<ProofNode> pn = state.getSelectedGoalNode();

        try {
            Parameters ruleParams = new Parameters();

            Evaluator<ProofNode> evaluator = new Evaluator<>(params, pn);
            call.getParameters().forEach((variable, expression) -> {
                        Value val = evaluator.eval(expression);
                        ruleParams.putValue(variable.getIdentifier(), convertValuesToTypedValues(val));
                    }
            );

            ProofRuleApplication proofRuleApplication = pr.makeApplication(pn.getData(), ruleParams);
            if (proofRuleApplication.getApplicability().equals(ProofRuleApplication.Applicability.APPLICABLE)) {
                ImmutableList<BranchInfo> applicationInfos = proofRuleApplication.getBranchInfo();
                if (applicationInfos.equals(BranchInfo.UNCHANGED)) {

                    //TODO handle unchanged case
                }
                if (applicationInfos.equals(BranchInfo.CLOSE)) {
                    //TODO handle closed case
                }
                Sequent sequent = pn.getData().getSequent();
                int numberOfChildrenExpected = applicationInfos.size();
                List<ProofNode> children = new ArrayList<>();
                applicationInfos.forEach(branchInfo -> {
                    System.out.println("branchInfo = " + branchInfo);
                    Sequent newSequent = createNewSequent(branchInfo, sequent);
                    ProofNode pnNew = new ProofNode(pn.getData(), proofRuleApplication, pn.getData().getHistory(), newSequent, pn.getData().getRootPVC());
                    children.add(pnNew);
                });
                assert numberOfChildrenExpected == children.size();
                state.getGoals().remove(pn);
                //state.getGoals().add(newCreatedGoals);
                //newcreatedgoals must be goalnode<ProofNode>
            } else {
                System.out.println("Warning command not applicable");
            }

        } catch (RuleException e) {
            throw new ScriptCommandNotApplicableException(e);
        }

        //TODO

    }

    private Sequent createNewSequent(BranchInfo branchInfo, Sequent oldSeq) {


        Sequent additions = branchInfo.getAdditions();
        Sequent deletions = branchInfo.getDeletions();
        Iterable<Pair<TermSelector, Term>> replacements = branchInfo.getReplacements();
        List<Pair<TermSelector, Term>> antecReplacements = new ArrayList<>();
        List<Pair<TermSelector, Term>> succReplacements = new ArrayList<>();
        replacements.forEach(termSelectorTermPair -> {
            if (termSelectorTermPair.getFst().equals(TermSelector.SequentPolarity.ANTECEDENT)) {
                antecReplacements.add(termSelectorTermPair);
            } else {
                succReplacements.add(termSelectorTermPair);
            }
        });


        List<ProofFormula> antec = changeSemisequent(additions.getAntecedent(), deletions.getAntecedent(), antecReplacements, oldSeq
                .getAntecedent());
        List<ProofFormula> succ = changeSemisequent(additions.getSuccedent(), deletions.getSuccedent(), succReplacements, oldSeq
                .getSuccedent());


        Sequent newSeq = new Sequent(antec, succ);
        return newSeq;

    }

    private List<ProofFormula> changeSemisequent(List<ProofFormula> add, List<ProofFormula> delete, List<Pair<TermSelector, Term>> change, List<ProofFormula> oldSemiSeq) {
        List<ProofFormula> newSemiSeq = new ArrayList<>(add);
        oldSemiSeq.forEach(proofFormula -> {
            //check if formula in deletions
            if (!delete.contains(proofFormula)) {
                //check if formula in changes
                change.forEach(termSelectorTermPair -> {
                    //do replacements
                });
                newSemiSeq.add(proofFormula);
            }
        });

        return newSemiSeq;
    }

    private Parameters.TypedValue convertValuesToTypedValues(Value val) {
        switch (val.getType()) {
            case STRING:
                return new Parameters.TypedValue(String.class, val.getData());
            case INT:
                return new Parameters.TypedValue(BigInteger.class, val.getData());
            default:
                throw new NotImplementedException();
        }
    }

    @Override
    public boolean isAtomic() {
        return true;
    }
}

