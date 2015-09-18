package edu.kit.iti.algover;

import edu.kit.iti.algover.parser.DafnyTree;
import edu.kit.iti.algover.symbex.PathConditionElement;

import java.io.File;
import java.util.LinkedList;

/**
 * ProofCenter manages several proof obligations
 * Created by sarah on 9/10/15.
 */
public class ProofCenter  {

   //list of all Proof obligations for one problemfile
   private LinkedList<Proof> proofs = new LinkedList<>();

    public LinkedList<Proof> getProofs() {
        return proofs;
    }

    /**
     * Has to check whether PO is duplicate TODO
     * @param proofs
     */
    public void setProofs(LinkedList<Proof> proofs) {
        this.proofs = new LinkedList<>();
        this.proofs = proofs;
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
     * Return the searched Proof Obligation if it exists
     * @param po
     * @return
     */
    public Proof searchForPO(String po){
        for (Proof proof : proofs) {
            if(proof.getName().equals(po)){
                return proof;
            }
        }
        return null;
    }

    public void insertProof(Proof p){
        Boolean conflict = false;

        if(proofs.size()==0){
            proofs.add(p);
        }else {
            for (Proof proof : proofs) {
                System.out.println("Checking: " + proof.getName());
                if (p.getName().equals(proof.getName())) {
                    conflict = true;
                    System.out.println("Conflicting names :" + p.getName() + "-----" + proof.getName());
                    break;
                }
            }
            if (conflict) {
                int id = p.getId();
                id = id+1;
                System.out.println("New ID"+id);
                Proof newProof = createProofObject(p.getAssumptions(), p.getToShow(), p.getCollected(), p.getCollected2(), id);
                System.out.println("New Name: " + newProof.getName());
                insertProof(newProof);

            }else{
                proofs.add(p);
                System.out.println("Added");
            }
        }
    }
    public Proof createProofObject(LinkedList<DafnyTree> ass, LinkedList<DafnyTree> show,
                 LinkedList<PathConditionElement> collected, LinkedList<PathConditionElement.AssertionType> collected2, int id){
        Proof nProof = new Proof(ass,show,collected,collected2,id);
        System.out.println("NewCall"+ nProof.getName());
        return nProof;

    }

}
