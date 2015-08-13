package edu.kit.iti.algover;

import edu.kit.iti.algover.PathCondition.AssertionType;
import edu.kit.iti.algover.parser.PseudoTree;
import edu.kit.iti.algover.util.ImmutableList;


public class SymbexState {

    private ImmutableList<PathCondition> pathConditions;
    private ImmutableList<PseudoTree> proofObligations;
    private AssertionType proofObligationType;
    private VariableMap currentMap;
    private PseudoTree program;

    public SymbexState() {
        pathConditions = ImmutableList.nil();
        currentMap = VariableMap.EMPTY;
    }

    public SymbexState(SymbexState state) {
        this.pathConditions = state.pathConditions;
        this.proofObligations = state.proofObligations;
        this.proofObligationType = state.proofObligationType;
        this.currentMap = state.currentMap;
        this.program = state.program;
    }

    public void addPathCondition(PathCondition pathCondition) {
        pathConditions = pathConditions.prepend(pathCondition);
    }

    public PseudoTree getProgram() {
        return program;
    }

    public VariableMap getMap() {
        return currentMap;
    }

    public void setMap(VariableMap newMap) {
        currentMap = newMap;
    }

    public void setProgram(PseudoTree program) {
        this.program = program;
    }

    public void setProofObligations(PseudoTree obligation, AssertionType type) {
        this.proofObligations = ImmutableList.single(obligation);
        this.proofObligationType = type;
    }

    public void setProofObligations(Iterable<PseudoTree> iterable, AssertionType type) {
        this.proofObligations = ImmutableList.from(iterable);
        this.proofObligationType = type;
    }

    public Iterable<PathCondition> getPathConditions() {
        return pathConditions;
    }

    public AssertionType getProofObligationType() {
        return proofObligationType;
    }

    public Iterable<PseudoTree> getProofObligations() {
        return proofObligations;
    }

}
