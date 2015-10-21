package edu.kit.iti.algover;

import edu.kit.iti.algover.Proof.ProofVerificationCondition;
import edu.kit.iti.algover.parser.DafnyTree;
import edu.kit.iti.algover.symbex.PathConditionElement;
import edu.kit.iti.algover.symbex.SymbexState;
import sun.awt.image.ImageWatched;

import java.io.File;
import java.util.LinkedList;

/**
 * Class that represents a proof with all its components and references
 * A proof object consists of a problem file, and a proof obligation (contained in a symbex state)
 *
 *
 */
public class ProofOld {
    public LinkedList<PathConditionElement> getCollected() {
        return collected;
    }

    public LinkedList<PathConditionElement.AssertionType> getCollected2() {
        return collected2;
    }

    private LinkedList<PathConditionElement> collected;
    private LinkedList<PathConditionElement.AssertionType> collected2;
    private LinkedList<DafnyTree> assumptions;
    private LinkedList<DafnyTree> toShow;



    public LinkedList<DafnyTree> getAssumptions() {
        return assumptions;
    }

    public void setAssumptions(LinkedList<DafnyTree> assumptions) {
        this.assumptions = assumptions;
    }

    public LinkedList<DafnyTree> getToShow() {
        return toShow;
    }

    public void setToShow(LinkedList<DafnyTree> toShow) {
        this.toShow = toShow;
    }

    public String getName() {
        return name;
    }

    private String name;

    public int getId() {
        return id;
    }

    private int id;


    public ProofOld(LinkedList<DafnyTree> ass, LinkedList<DafnyTree> show,
                 LinkedList<PathConditionElement> collected, LinkedList<PathConditionElement.AssertionType> collected2, int id){
        this.setAssumptions(ass);
        this.setToShow(show);
        this.collected = collected;
        this.collected2 = collected2;
        this.id = id;
        name = creatName();

    }

    private String creatName() {
        //label fehlt noch id muss dann ersetzt werden
        String name = "";


        for (PathConditionElement pathConditionElement : collected) {
            name+=pathConditionElement.getType()+"\\";
        }
        for (PathConditionElement.AssertionType assertionType : collected2) {
            name+=assertionType.toString()+"\\";
        }
        name+=id;
        return name;
    }


    public String proofToString(){
       // ProofVerificationCondition pvc = new ProofVerificationCondition(assumptions,toShow);
        String po = "";
        for (DafnyTree assumption : assumptions) {
            po+= assumption.toStringTree() +",\n";
        }
        po += "==>\n";

        for (DafnyTree dafnyTree : toShow) {
            po+= dafnyTree.toStringTree()+"\n";
        }

        return po;
    }
}
