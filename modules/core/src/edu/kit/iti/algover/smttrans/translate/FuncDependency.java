//package edu.kit.iti.algover.smttrans.translate;
//
//import java.util.LinkedHashSet;
//import java.util.List;
//
//import edu.kit.iti.algover.smttrans.data.Axiom;
//import edu.kit.iti.algover.smttrans.data.AxiomContainer;
//import edu.kit.iti.algover.smttrans.data.Operation;
//
//public class FuncDependency extends Dependency {
//
//    private Operation op;
//
//    public FuncDependency(Operation o, Type t) {
//        super(t);
//        this.op = o;
//    }
//
//    @Override
//    public LinkedHashSet<String> instantiate() {
//        LinkedHashSet<String> inst = new LinkedHashSet<>();
//        
//        inst.addAll(AxiomContainer.instantiateSort(op.getType(), t)); 
//        for (Axiom a : op.getInstantiations()) {
//            
//            inst.add(AxiomContainer.instantiateAxiom(a,t));
//        }
//        
//       // inst.add(AxiomContainer.instantiateAxiom(Axiom.SET_1, t));//debug
//        //System.out.println(inst.toString());
//        return inst;
//    }
//    @Override
//    public String toString() {
//        return op.name() + " : " + this.t.toString();
//    }
//
//    @Override
//    public int hashCode() {
//        final int prime = 31;
//        int result = super.hashCode();
//        result = prime * result + ((op == null) ? 0 : op.hashCode());
//        return result;
//    }
//
//    @Override
//    public boolean equals(Object obj) {
//        if (this == obj)
//            return true;
//        if (!super.equals(obj))
//            return false;
//        if (!(obj instanceof FuncDependency))
//            return false;
//        FuncDependency other = (FuncDependency) obj;
//        if (op != other.op)
//            return false;
//        return true;
//    }
//
//    @Override
//    public LinkedHashSet<String> declare() {
//        LinkedHashSet<String> inst = new LinkedHashSet<>();
//        
//        inst.addAll(AxiomContainer.declareSort(op.getType(), t)); 
//        for (Axiom a : op.getInstantiations()) {
//            
//            inst.add(AxiomContainer.declareAxiom(a,t));
//        }
//        
//        return inst;
//    }
//
//}
