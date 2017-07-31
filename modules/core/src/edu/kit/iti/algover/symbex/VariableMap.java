///*
// * This file is part of AlgoVer.
// *
// * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
// */
//package edu.kit.iti.algover.symbex;
//
//import java.util.Iterator;
//import java.util.LinkedList;
//import java.util.List;
//
//import edu.kit.iti.algover.parser.DafnyTree;
//import edu.kit.iti.algover.util.ASTUtil;
//import edu.kit.iti.algover.util.ImmutableList;
//import edu.kit.iti.algover.util.Pair;
//
//
///*
// * This is badly deprecated by now.
// *
// * PLEASE REMOVE EVERY REFERENCE TO THIS CLASS.
// *
// */
//@Deprecated
//public final class VariableMap implements Iterable<Pair<String, DafnyTree>> {
//
//    public static final VariableMap EMPTY = new VariableMap(ImmutableList.nil());
//
//    private final ImmutableList<DafnyTree> assignments;
//
//    public VariableMap assign(String var, DafnyTree value) {
//        return new VariableMap(assignments.append(ASTUtil.assign(ASTUtil.id(var), value)));
//    }
//
//    public VariableMap(ImmutableList<DafnyTree> assignments) {
//        this.assignments = assignments;
//    }
//
//    public String toHistoryString() {
//        StringBuilder sb = new StringBuilder();
//        ImmutableList<DafnyTree> vm = assignments;
//        while(vm != null) {
//            String nl = sb.length() == 0 ? "" : "\n";
//            DafnyTree ass = vm.getHead();
//            sb.insert(0, ass.toStringTree() + nl);
//            vm = vm.getTail();
//        }
//        return sb.toString();
//    }
//
//    @Override
//    public String toString() {
//        return toHistoryString();
//    }
//
//    /**
//     * Checks whether this map has an assignment to the given variable.
//     *
//     * @param variableName
//     *            the variable name to check, not <code>null</code>
//     * @return true, if there is an assignment/havoc for the variable.
//     */
//    public boolean hasAssignmentTo(String variableName) {
//        ImmutableList<DafnyTree> vm = assignments;
//        while (vm != null) {
//            if (vm.getHead().getChild(0).getText().equals(variableName)) {
//                return true;
//            }
//            vm = vm.getTail();
//        }
//        return false;
//    }
//
//
//    @Override
//    public Iterator<Pair<String, DafnyTree>> iterator() {
//        List<Pair<String, DafnyTree>> result = toList();
//        return result.iterator();
//    }
//
//    public List<Pair<String, DafnyTree>> toList() {
//        LinkedList<Pair<String, DafnyTree>> result = new LinkedList<>();
//        for (DafnyTree ass : assignments) {
//            result.add(new Pair<>(ass.getChild(0).getText(), ass.getChild(1)));
//        }
//        return result;
//    }
//
//    @Deprecated
//    public DafnyTree instantiate(DafnyTree expression) {
//        System.err.println("Instantiation is no longer possible on sytax level due to heap deps");
//        return expression;
//    }
//
//}
