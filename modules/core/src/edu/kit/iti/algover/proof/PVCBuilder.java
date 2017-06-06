/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.proof;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;

import edu.kit.iti.algover.ProgramDatabase;
import edu.kit.iti.algover.dafnystructures.DafnyDecl;
import edu.kit.iti.algover.dafnystructures.DafnyMethod;
import edu.kit.iti.algover.data.BuiltinSymbols;
import edu.kit.iti.algover.data.MapSymbolTable;
import edu.kit.iti.algover.data.SuffixSymbolTable;
import edu.kit.iti.algover.data.SymbolTable;
import edu.kit.iti.algover.parser.DafnyParser;
import edu.kit.iti.algover.parser.DafnyTree;
import edu.kit.iti.algover.script.ScriptTree;
import edu.kit.iti.algover.symbex.AssertionElement;
import edu.kit.iti.algover.symbex.PathConditionElement;
import edu.kit.iti.algover.symbex.SymbexPath;
import edu.kit.iti.algover.term.FunctionSymbol;
import edu.kit.iti.algover.term.Sort;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.term.builder.TermBuildException;
import edu.kit.iti.algover.term.builder.TreeTermTranslator;
import edu.kit.iti.algover.util.ImmutableList;
import edu.kit.iti.algover.util.TreeUtil;
import edu.kit.iti.algover.util.Util;

/**
 * A PVC corresponds to a symbexpath. So it consists of assignments on the path through the program of
 * pathconditions and of a goal to prove. In addition it is uniquely identified by its ID. This ID has to be given from a central instance
 * New attempt to implement a PVC Builder.
 *
 * REVIEW: Is this a builder for method PVCs? I assume so. If so, rename it accordngly.
 *
 * This class is not ready for multi-threading.
 *
 * Created by sarah on 8/18/16.
 */
public class PVCBuilder {
    /**
     * Counter for IDs for TopFormulas
     */
    private int formulaCounter = 0;

    /**
     * ID of proof verification condition, has to be unique
     */
    // REVIEW: What are the benefits of an integer ID?
    /* I think it would rather be very important that the PO/PVCs have
     * a unique srting id. In KeY, they had numbers at one point. Adding
     * a single new method threw every finished proof overboard.
     *
     * Are there benefits in integer Ids?
     */
    private int pvcID;

    /**
     * local script of pvc, is identified by id
     */
    private ScriptTree localScript;

    /**
     * List of terms for the "toplevel" formula representing assumptions with a wrapper containing additional information
     */
    // REVIEW: Why withInfo? Is this not implied by the type?
    private final List<TopFormula> assumptionsWithInfo;

    /**
     * List of terms for the "toplevel" formula representing goals with a wrapper containing additional information
     */
    // REVIEW: Why withInfo? Is this not implied by the type?
    private final List<TopFormula> goalWithInfo;

    /**
     * Path through program which represents state of this pvc
     */
    private SymbexPath pathThroughProgram;

    /**
     * DafnyDecl this PVC belongs to
     */
    private DafnyDecl declaration;

    private SymbolTable symbolTable;

    public PVCBuilder(){
        this.assumptionsWithInfo = new LinkedList<>();
        this.goalWithInfo = new LinkedList<>();
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

    public DafnyDecl getDeclaration() {
        return declaration;
    }

    public PVCBuilder setDeclaration(DafnyDecl decl) {
        this.declaration = decl;
        return this;
    }

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

    public PVC build() throws TermBuildException {
        formulaCounter = 0;
        this.symbolTable = makeSymbolTable();
        buildAssumptionTerms();
        buildAssertionTerms();
        return new PVC(this);
    }

    private SymbolTable makeSymbolTable() {

        Collection<FunctionSymbol> map = new ArrayList<>();

        // FIXME: This builder is probably meant only for methods. store method instead of declaration
        DafnyMethod method = (DafnyMethod) declaration;

        for (DafnyTree decl : ProgramDatabase.getAllVariableDeclarations(method.getRepresentation())) {
            String name = decl.getChild(0).toString();
            Sort sort = TreeUtil.toSort(decl.getChild(1));
            map.add(new FunctionSymbol(name, sort));
        }

        MapSymbolTable st = new SuffixSymbolTable(new BuiltinSymbols(), map);
        return st;
    }

    /**
     *
     * Iterate over pathconditions and build the toplevel formulas for this PVC
     * @param pathConditions
     * @throws TermBuildException
     */
    private void buildAssumptionTerms() throws TermBuildException {

        TreeTermTranslator ttt = new TreeTermTranslator(symbolTable);
        for(PathConditionElement pce : pathThroughProgram.getPathConditions()) {

            // FIXME refactor
            Term term = ttt.build(pce.getVariableMap(), pce.getExpression());
            final TopFormula tf = buildTopFormula(ttt,
                    pce.getExpression(), pathThroughProgram.getAssignmentHistory(), pce);
            assumptionsWithInfo.add(tf);
        }


    }

    /**
     * Build the Terms for creating the Toplevel-Formulas from assertions
     * @param assertions
     */
    private void buildAssertionTerms() {

        // XXX Caution: If you invoke PVCBuilder with a SymbexPath with severl assertions
        // they will be illegally combined using disjunction here.

        // FIXME: Same as above with assumptions but with assertions.
//
//        SymbexPathToTopFormula septf;
//          TreeTermTranslator ttt;
//
//
//        //= new SymbexPathToTopFormula(parent.getRepresentation());
//        //TreeTermTranslator ttt = new TreeTermTranslator(septf.getSymbolTable());
//        for(AssertionElement ae : assertions){
//            if(ae.getType() != AssertionElement.AssertionType.VARIANT_DECREASED) {
//                septf = new SymbexPathToTopFormula(declaration.getRepresentation());
//                ttt = new TreeTermTranslator(septf.getSymbolTable());
//
//                final TopFormula tf = buildTopFormulaAssert(ttt, ae.getExpression(), pathThroughProgram.getAssignmentHistory(), ae);
//                goalWithInfo.add(tf);
//            }else{
//
//                //TODO its a hack
//                septf = new SymbexPathToTopFormula(declaration.getRepresentation());
//                ttt = new TreeTermTranslator(
//                        septf.getSymbolTable().addFunctionSymbol(
//                                new FunctionSymbol(ae.getExpression().getChild(0).getText(),
//                                        Sort.INT, Collections.emptyList())));
//
//                goalWithInfo.add(createVariantGoal(ae, ttt));
//            }
//        }


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

        // FIXME: Missing here: Assignment to variant variable
//        return buildTopFormulaAssert(ttt, toTranslate, pathThroughProgram.getMap().assign(expression.getChild(0).getText(), decreasesTerm), ae);
        return buildTopFormulaAssert(ttt, toTranslate, pathThroughProgram.getAssignmentHistory(), ae);
    }

    /**
     * Build the Terms for creating the ToplevelFormulas from assumptions
     * @param
     */
    // REVIEW: term is embedded into let term?
    // We need a fresh concept of translating
    private TopFormula buildTopFormula(TreeTermTranslator ttt, DafnyTree expression, ImmutableList<DafnyTree> immutableList, PathConditionElement pce){
        TopFormula tf = null;
        try {
            Term term = ttt.build(expression);
            Term letTerm = ttt.build(immutableList, expression);
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

    private TopFormula buildTopFormulaAssert(TreeTermTranslator ttt, DafnyTree expression, ImmutableList<DafnyTree> map, AssertionElement ae){
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
