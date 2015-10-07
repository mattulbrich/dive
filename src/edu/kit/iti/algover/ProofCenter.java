package edu.kit.iti.algover;

import edu.kit.iti.algover.parser.DafnyTree;
import edu.kit.iti.algover.symbex.PathConditionElement;

import java.io.File;
import java.util.LinkedList;

/**
 * ProofOldCenter manages several ProofOld obligations
 * Created by sarah on 9/10/15.
 */
public class ProofCenter  {

   //list of all ProofOld obligations for one problemfile
   private LinkedList<ProofOld> ProofOlds = new LinkedList<>();

    public LinkedList<ProofOld> getProofOlds() {
        return ProofOlds;
    }

    /**
     * Has to check whether PO is duplicate TODO
     * @param ProofOlds
     */
    public void setProofOlds(LinkedList<ProofOld> ProofOlds) {
        this.ProofOlds = new LinkedList<>();
        this.ProofOlds = ProofOlds;
    }

    public File getProblemFile() {
        return problemFile;
    }

    public void setProblemFile(File problemFile) {
        this.problemFile = problemFile;
    }

    File problemFile;


   private static ProofCenter instance = null;
   protected ProofCenter() {

   }
   public static ProofCenter getInstance() {
      if(instance == null) {
         instance = new ProofCenter();
      }
      return instance;
   }

    /**
     * Return the searched ProofOld Obligation if it exists
     * @param po
     * @return
     */
    public ProofOld searchForPO(String po){
        for (ProofOld ProofOld : ProofOlds) {
            if(ProofOld.getName().equals(po)){
                return ProofOld;
            }
        }
        return null;
    }

    public void insertProofOld(ProofOld p){
        Boolean conflict = false;

        if(ProofOlds.size()==0){
            ProofOlds.add(p);
        }else {
            for (ProofOld ProofOld : ProofOlds) {
                System.out.println("Checking: " + ProofOld.getName());
                if (p.getName().equals(ProofOld.getName())) {
                    conflict = true;
                    System.out.println("Conflicting names :" + p.getName() + "-----" + ProofOld.getName());
                    break;
                }
            }
            if (conflict) {
                int id = p.getId();
                id = id+1;
                System.out.println("New ID"+id);
                ProofOld newProofOld = createProofOldObject(p.getAssumptions(), p.getToShow(), p.getCollected(), p.getCollected2(), id);
                System.out.println("New Name: " + newProofOld.getName());
                insertProofOld(newProofOld);

            }else{
                ProofOlds.add(p);
                System.out.println("Added");
            }
        }
    }
    public ProofOld createProofOldObject(LinkedList<DafnyTree> ass, LinkedList<DafnyTree> show,
                 LinkedList<PathConditionElement> collected, LinkedList<PathConditionElement.AssertionType> collected2, int id){
        ProofOld nProofOld = new ProofOld(ass,show,collected,collected2,id);
        System.out.println("NewCall"+ nProofOld.getName());
        return nProofOld;

    }

}
