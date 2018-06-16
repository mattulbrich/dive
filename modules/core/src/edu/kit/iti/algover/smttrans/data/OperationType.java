//package edu.kit.iti.algover.smttrans.data;
//
//import java.util.ArrayList;
//import java.util.Arrays;
//import java.util.List;
//
//public enum OperationType {
//
//    ARR, ARR2, SET, MULTISET, INT, BOOL, SORT, ANY, NONE, SEQ;
//
//    private String smt;
//    private List<String> dependencies = new ArrayList<>();
//
//    static {
//        ARR.smt = "Arr";
//        ARR.dependencies = Arrays.asList(); //"Heap","heap Heap"
//        ARR2.smt = "Arr2";
//        SET.smt = "Set";
//        MULTISET.smt = "mSet";
//        INT.smt = "Int";
//        BOOL.smt = "Bool";
//        SEQ.smt = "Seqq";
//        SORT.smt = "SORT";
//        SORT.dependencies = Arrays.asList(); //"Heap","heap Heap"
//        ANY.smt = "ANY";
//        NONE.smt = "NONE";
//    }
//
//    public String getSMT() {
//        return smt;
//    }
//
//    public List<String> getDependencies() {
//        List<String> inst = new ArrayList<>();
//        for (String d : dependencies) {
//            StringBuilder sb = new StringBuilder();
//            sb.append("(declare-");
//            if (d.contains(" ")) {
//                sb.append("const ");
//                sb.append(d);
//            } else {
//                sb.append("sort ");
//                sb.append(d + " 0");
//            }
//            sb.append(")");
//            inst.add(sb.toString());
//        }
//
//        return inst;
//    }
//
//    public List<String> getDependenciesDecl() {
//        List<String> decl = new ArrayList<>();
//        for (String d : dependencies) {
//            StringBuilder sb = new StringBuilder();
//            sb.append("(inst-");
//            if (d.contains(" ")) {
//                sb.append("const ");
//                String[] parts = d.split(" ");
//                sb.append(parts[0]);
//                sb.append(" :: ");
//                sb.append(parts[1]);
//
//            } else {
//                sb.append("sort :: ");
//                sb.append(d);
//            }
//            sb.append(")");
//            decl.add(sb.toString());
//        }
//
//        return decl;
//    }
//}
