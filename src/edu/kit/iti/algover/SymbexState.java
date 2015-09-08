package edu.kit.iti.algover;

import edu.kit.iti.algover.PathConditionElement.AssertionType;
import edu.kit.iti.algover.parser.PseudoTree;
import edu.kit.iti.algover.util.ImmutableList;


public class SymbexState {

    private ImmutableList<PathConditionElement> pathConditions;
    private ImmutableList<PseudoTree> proofObligations;
    private AssertionType proofObligationType;
    private VariableMap currentMap;
    private PseudoTree blockToExecute;
    private final PseudoTree function;

    public SymbexState(PseudoTree function) {
        this.pathConditions = ImmutableList.nil();
        this.currentMap = VariableMap.EMPTY;
        this.function = function;
    }

    public SymbexState(SymbexState state) {
        this.pathConditions = state.pathConditions;
        this.proofObligations = state.proofObligations;
        this.proofObligationType = state.proofObligationType;
        this.currentMap = state.currentMap;
        this.blockToExecute = state.blockToExecute;
        this.function = state.function;
    }

    public void addPathCondition(PathConditionElement pathCondition) {
        pathConditions = pathConditions.prepend(pathCondition);
    }

    public VariableMap getMap() {
        return currentMap;
    }

    public void setMap(VariableMap newMap) {
        currentMap = newMap;
    }

    public PseudoTree getFunction() {
        return function;
    }

    public PseudoTree getBlockToExecute() {
        return blockToExecute;
    }

    public void setBlockToExecute(PseudoTree program) {
        this.blockToExecute = program;
    }

    public void setProofObligations(PseudoTree obligation, AssertionType type) {
        this.proofObligations = ImmutableList.single(obligation);
        this.proofObligationType = type;
    }

    public void setProofObligations(Iterable<PseudoTree> iterable, AssertionType type) {
        this.proofObligations = ImmutableList.from(iterable);
        this.proofObligationType = type;
    }

    public Iterable<PathConditionElement> getPathConditions() {
        return pathConditions;
    }

    public AssertionType getProofObligationType() {
        return proofObligationType;
    }

    public Iterable<PseudoTree> getProofObligations() {
        return proofObligations;
    }

}
