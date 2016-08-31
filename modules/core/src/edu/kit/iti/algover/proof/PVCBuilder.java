package edu.kit.iti.algover.proof;

import edu.kit.iti.algover.parser.DafnyTree;
import edu.kit.iti.algover.project.DafnyDecl;
import edu.kit.iti.algover.script.ScriptTree;
import edu.kit.iti.algover.symbex.AssertionElement;
import edu.kit.iti.algover.symbex.PathConditionElement;
import edu.kit.iti.algover.symbex.SymbexPath;
import edu.kit.iti.algover.symbex.VariableMap;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.term.builder.TermBuildException;
import edu.kit.iti.algover.term.builder.TermBuilder;
import edu.kit.iti.algover.term.builder.TreeTermTranslator;
import edu.kit.iti.algover.util.ImmutableList;

import java.util.Collections;
import java.util.LinkedList;
import java.util.List;

/**
 * A PVC corresponds to a symbexpath. So it consists of assignments on the path through teh program of
 * pathconditions and of a goal to prove. In addition it is uniquely identified by its OIC. This ID has to be given from a central instance
 * New attempt to implement a PVC Builder
 * Created by sarah on 8/18/16.
 */
public class PVCBuilder {
    /**
     * Counter for IDs for TopFormulas
     */
    private int formulaCounter;

    /**
     * ID of proof verification condition, has to be unique
     */
    private int pvcID;

    /**
     * local script of pvc, is identified by id
     */
    private ScriptTree localScript;

    /**
     * List of terms for the "toplevel" formula representing assumptions with a wrapper containing additional information
     */
    private List<TopFormula> assumptionsWithInfo;

    /**
     * List of terms for the "toplevel" formula representing goals with a wrapper containing additional information
     */
    private List<TopFormula> goalWithInfo;

    public int getFormulaCounter() {
        return formulaCounter;
    }


    public int getPvcID() {
        return pvcID;
    }

    public ScriptTree getLocalScript() {
        return localScript;
    }

    public List<TopFormula> getAssumptionsWithInfo() {
        return assumptionsWithInfo;
    }



    public List<TopFormula> getGoalWithInfo() {
        return goalWithInfo;
    }



    public SymbexPath getPathThroughProgram() {
        return pathThroughProgram;
    }

    public String getPvcName() {
        return pvcName;
    }

    public PVCBuilder setPvcName(String pvcName) {
        this.pvcName = pvcName;
        return this;
    }

    public DafnyDecl getParent() {
        return parent;
    }

    public PVCBuilder setParent(DafnyDecl parent) {
        this.parent = parent;
        return this;
    }

    /**

     * Path through programm
     */
    private SymbexPath pathThroughProgram;

    private String pvcName;



    /**
     *DafnyDecl this PVC belongs to
     */
    private DafnyDecl parent;

    public PVCBuilder setPvcID(int pvcID) {
        this.pvcID = pvcID;
        return this;
    }

    public PVCBuilder setLocalScript(ScriptTree localScript) {
        this.localScript = localScript;
        return this;
    }



    public PVCBuilder setPathThroughProgram(SymbexPath pathThroughProgram) {
        this.pathThroughProgram = pathThroughProgram;
        return this;
    }


    public PVCBuilder(int globalID){
        this.pvcID = globalID;
        //initialize data structures
        this.formulaCounter = 0;
        this.assumptionsWithInfo = new LinkedList<TopFormula>();
        this.goalWithInfo = new LinkedList<TopFormula>();


    }


    public PVC buildPVC(SymbexPath path, DafnyDecl parent){
        //set the parents and the pointer to teh symbexpath object which contains further information which may be needed later on
        this.parent = parent;
        setPathThroughProgram(path);
        this.pvcName = path.getPathIdentifier();
        //extract Assumptions
        //extract Goals
        //generate TopFormulas

        buildTerms(path.getPathConditions());
        buildAssertionTerms(path.getProofObligations());
        //extracting Assignments is done for each TopFormula
        return new PVC(this);
    }

    /**
     *
     * Iterate over pathconditions and build the toplevel formulas for this PVC
     * @param pathConditions
     */
    private void buildTerms(ImmutableList<PathConditionElement> pathConditions) {

        SymbexPathToTopFormula septf = new SymbexPathToTopFormula(parent.getRepresentation());
        TreeTermTranslator ttt = new TreeTermTranslator(septf.getSymbolTable());
        for(PathConditionElement pce : pathConditions){

            final TopFormula tf = buildTopFormula(ttt, pce.getExpression(), pathThroughProgram.getMap(), pce);
            assumptionsWithInfo.add(tf);
        }


    }

    /**
     * Build the Terms for creating the ToplevelFormulas from assertions
     * @param assertions
     */
    private void buildAssertionTerms(ImmutableList<AssertionElement> assertions) {

        SymbexPathToTopFormula septf = new SymbexPathToTopFormula(parent.getRepresentation());
        TreeTermTranslator ttt = new TreeTermTranslator(septf.getSymbolTable());
        for(AssertionElement ae : assertions){

            final TopFormula tf = buildTopFormulaAssert(ttt, ae.getExpression(), pathThroughProgram.getMap(), ae);
            goalWithInfo.add(tf);
        }


    }

    /**
     * Build the Terms for creating the ToplevelFormulas from assumptions
     * @param
     */
    private TopFormula buildTopFormula(TreeTermTranslator ttt, DafnyTree expression, VariableMap map, PathConditionElement pce){
        TopFormula tf = null;
        try {
            Term term = ttt.build(expression);
            Term letTerm = ttt.build(map, expression);
            int line = pce.getExpression().token.getLine();
            if(line <=0 ){
                   line = pce.getExpression().getChild(0).token.getLine();
                }
            tf = new TopFormula(term, letTerm, formulaCounter, this.pathThroughProgram, line, pce, this.pvcID);
            formulaCounter++;
        } catch (TermBuildException e) {
            e.printStackTrace();
        }
        return tf;
    }

    private TopFormula buildTopFormulaAssert(TreeTermTranslator ttt, DafnyTree expression, VariableMap map, AssertionElement ae){
        TopFormula tf = null;
        try {
            Term term = ttt.build(expression);
            Term letTerm = ttt.build(map, expression);
            int line = ae.getExpression().token.getLine();
            if(line <=0 ){
                line = ae.getExpression().getChild(0).token.getLine();
            }
            tf = new TopFormula(term, letTerm, formulaCounter, this.pathThroughProgram, line, ae, this.pvcID);
            formulaCounter++;
        } catch (TermBuildException e) {
            e.printStackTrace();
        }
        return tf;
    }
    /*
    int i = 0;
        System.out.println(path.getPathIdentifier());
        //get pathconditions
        ImmutableList<PathConditionElement> pathConditions = path.getPathConditions();
        //getProofObligation
        ImmutableList<AssertionElement> pos = path.getProofObligations();
        SymbexPathToTopFormula septf = new SymbexPathToTopFormula(parent);
        TreeTermTranslator ttt = new TreeTermTranslator(septf.getSymbolTable());
        for(PathConditionElement pce : pathConditions){
            try {
                Term t = ttt.build(pce.getExpression());
                Term let = ttt.build(path.getMap(), pce.getExpression());
                int line = pce.getExpression().token.getLine();
                if(line <=0 ){
                   line = pce.getExpression().getChild(0).token.getLine();
                }
                TopFormula tf = new TopFormula(t,let, i , path, line);
                System.out.println(tf.toString());
                //this.assumptionsWithInfo.add(tf);
            } catch (TermBuildException e) {
                e.printStackTrace();
            }
            i++;

        }
        for(AssertionElement po : pos){
            try {
                Term t = ttt.build(po.getExpression());
                Term let = ttt.build(path.getMap(), po.getExpression());
                int line = po.getExpression().token.getLine();
                if(line <= 0){
                    line = po.getExpression().getChild(0).token.getLine();
                }
                TopFormula tf = new TopFormula(t, let, i, path, line);
                System.out.println("Goal: "+tf.toString());
            } catch (TermBuildException e) {
                e.printStackTrace();
            }

          //  System.out.println("PO: "+po);

     */

}
