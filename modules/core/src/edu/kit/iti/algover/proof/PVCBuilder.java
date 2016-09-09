package edu.kit.iti.algover.proof;

import edu.kit.iti.algover.parser.DafnyParser;
import edu.kit.iti.algover.parser.DafnyTree;
import edu.kit.iti.algover.dafnystructures.DafnyDecl;
import edu.kit.iti.algover.script.ScriptTree;
import edu.kit.iti.algover.symbex.AssertionElement;
import edu.kit.iti.algover.symbex.PathConditionElement;
import edu.kit.iti.algover.symbex.SymbexPath;
import edu.kit.iti.algover.symbex.VariableMap;
import edu.kit.iti.algover.term.FunctionSymbol;
import edu.kit.iti.algover.term.Sort;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.term.builder.TermBuildException;
import edu.kit.iti.algover.term.builder.TreeTermTranslator;
import edu.kit.iti.algover.util.ImmutableList;
import org.antlr.runtime.Token;
import org.antlr.runtime.tree.Tree;

import java.util.Collections;
import java.util.Iterator;
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
        this.assumptionsWithInfo = new LinkedList<>();
        this.goalWithInfo = new LinkedList<>();


    }


    public PVC buildPVC(SymbexPath path, DafnyDecl parent){
        //set the parents and the pointer to the symbexpath object which contains further information which may be needed later on
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
     * Build the Terms for creating the Toplevel-Formulas from assertions
     * @param assertions
     */
    private void buildAssertionTerms(ImmutableList<AssertionElement> assertions) {

        SymbexPathToTopFormula septf;
          TreeTermTranslator ttt;


        //= new SymbexPathToTopFormula(parent.getRepresentation());
        //TreeTermTranslator ttt = new TreeTermTranslator(septf.getSymbolTable());
        for(AssertionElement ae : assertions){
            if(ae.getType() != AssertionElement.AssertionType.VARIANT_DECREASED) {
                septf = new SymbexPathToTopFormula(parent.getRepresentation());
                ttt = new TreeTermTranslator(septf.getSymbolTable());

                final TopFormula tf = buildTopFormulaAssert(ttt, ae.getExpression(), pathThroughProgram.getMap(), ae);
                goalWithInfo.add(tf);
            }else{

                //TODO its a hack
                septf = new SymbexPathToTopFormula(parent.getRepresentation());
                ttt = new TreeTermTranslator(septf.getSymbolTable().addFunctionSymbol(new FunctionSymbol(ae.getExpression().getChild(0).getText(), Sort.INT, Collections.emptyList())));

                goalWithInfo.add(createVariantGoal(ae, ttt));
            }
        }


    }

    private TopFormula createVariantGoal(AssertionElement ae, TreeTermTranslator ttt) {

        DafnyTree expression = ae.getExpression();

       // if(expression.getType() == DafnyParser.NOETHER_LESS){
            DafnyTree toTranslate = new DafnyTree(DafnyParser.AND);
            DafnyTree decreasesTerm = null;
           // Token t = null;
            if(expression.getChild(1).getType() == DafnyParser.LISTEX){
                decreasesTerm =   expression.getChild(1).getChild(0);
            //    t = decreasesTerm.getToken();
            }

            DafnyTree strictlySmaller = new DafnyTree(DafnyParser.GT);
          //  strictlySmaller.setTokenStartIndex(t.getTokenIndex());
            strictlySmaller.addChild(expression.getChild(0));
            strictlySmaller.addChild(decreasesTerm);


            DafnyTree geqZero = new DafnyTree(DafnyParser.GE);
            geqZero.addChild(decreasesTerm);
            geqZero.addChild(new DafnyTree(DafnyParser.ID, "0"));
          //  geqZero.setTokenStartIndex(t.getTokenIndex());

            toTranslate.addChild(strictlySmaller);
            toTranslate.addChild(geqZero);
        //    toTranslate.setTokenStartIndex(t.getTokenIndex());


      //  }
        return buildTopFormulaAssert(ttt, toTranslate, pathThroughProgram.getMap().assign(expression.getChild(0).getText(), decreasesTerm), ae);
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
       // if(ae.getType() == AssertionElement.AssertionType.VARIANT_DECREASED){
       //     System.out.println("Term Building of varaint decreased not supported yet");

        //}else {
            try {

                Term term = ttt.build(expression);
                Term letTerm = ttt.build(map, expression);
                int line = ae.getExpression().token.getLine();
                Iterator<DafnyTree> iter = ae.getExpression().getChildren().iterator();
                while(line <= 0 && iter.hasNext()){
                    line = iter.next().token.getLine();
                }

//                if (line <= 0) {
//                    line = ae.getExpression().getChild(0).token.getLine();
//                }
                tf = new TopFormula(term, letTerm, formulaCounter, this.pathThroughProgram, line, ae, this.pvcID);
                formulaCounter++;
            } catch (TermBuildException e) {
                e.printStackTrace();
            }
      //  }
        return tf;
    }

}
