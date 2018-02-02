package edu.kit.iti.algover.script.data;

import edu.kit.iti.algover.proof.ProofNode;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

/**
 * Object representing a state
 *
 * @author S.Grebing
 */

public class State<T> {


    /**
     * All goalnodes in this state
     */
    private List<ProofNode> goals;


    /**
     * Currently selected GoalNode
     */
    private ProofNode selectedGoalNode;

    private boolean errorState;


    public State(List<ProofNode> goals, int n) {
        this(goals, goals.get(n));
    }


    public State(Collection<ProofNode> goals, ProofNode selected) {
        this.goals = new ArrayList<>(goals);
        this.selectedGoalNode = selected;
        assert selected == null || goals.contains(selected);
    }

    public State(ProofNode goal) {
        assert goal != null;
        goals = new ArrayList<>();
        goals.add(goal);
        setSelectedGoalNode(goal);
    }

    public ProofNode getSelectedGoalNode() {
        if (selectedGoalNode == null) {
            throw new IllegalStateException("no selected node");
        } else {
            if (getGoals().size() == 1) {
                selectedGoalNode = getGoals().get(0);
            }
            return selectedGoalNode;
        }
    }

    public List<ProofNode> getGoals() {
        return goals;
    }

    public void setSelectedGoalNode(ProofNode gn) {
        this.selectedGoalNode = gn;
    }

    /**
     * TODO correct this method, atm does nothing helpful!
     *
     * @return
     */
    public State<T> copy() {
        List<ProofNode> copiedGoals = new ArrayList<>(goals);
        ProofNode refToSelGoal = selectedGoalNode;
        return new State<T>(copiedGoals, refToSelGoal);
    }

    public String toString() {
        if (selectedGoalNode == null) {
            return "No Goal selected";
        } else {
            return selectedGoalNode.toString();
        }

    }

    public boolean isErrorState() {
        return this.errorState;
    }

    public void setErrorState(boolean errorState) {
        this.errorState = errorState;
    }
}

