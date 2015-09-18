package edu.kit.iti.algover;

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
public class Proof {
    private LinkedList<PathConditionElement> collected;
    private LinkedList<PathConditionElement.AssertionType> collected2;

    private LinkedList<DafnyTree> assumptions;

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

    public String name;
    private LinkedList<DafnyTree> toShow;

    public Proof(LinkedList<DafnyTree> ass, LinkedList<DafnyTree> show,
                 LinkedList<PathConditionElement> collected, LinkedList<PathConditionElement.AssertionType> collected2){
        this.setAssumptions(ass);
        this.setToShow(show);
        this.collected = collected;
        this.collected2 = collected2;
        name = creatName();
    }

    private String creatName() {
        //label fehlt noch
        String name = "";
        for (PathConditionElement.AssertionType assertionType : collected2) {
            name+=assertionType.toString()+"\\";
        }

        for (PathConditionElement pathConditionElement : collected) {
            name+=pathConditionElement.getType()+"\\";
        }
        return name;
    }


    public String proofToString(){
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
