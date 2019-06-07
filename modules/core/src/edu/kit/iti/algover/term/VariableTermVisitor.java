/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
///*
// * This file is part of AlgoVer.
// *
// * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
// */
//package edu.kit.iti.algover.term;
//
//import java.util.LinkedList;
//import java.util.List;
//
///**
// * Created by sarah on 8/30/16.
// * TODO Add class documentation
// * TODO Choose a more self-explanatory class name
// */
//// This class does not seem to be used.
//@Deprecated
//public class VariableTermVisitor extends DefaultTermVisitor<Object, List<String>, RuntimeException> {
//
//
//    @Override
//    protected List<String> defaultVisit(Term term, Object arg) {
//        List<Term> subterms = term.getSubterms();
//        List<String> list = new LinkedList<>();
//        for(Term t: subterms){
////            System.out.println("TermVisitor "+term.toString()+"\n");
////            System.out.println("Subterm: "+t.toString() + " type "+t.getClass());
//
//            list.addAll(t.accept(this, arg));
//        }
//        return list;
//
//    }
//
//    /**
//     * At the Moment there exits a problem when an ApplTerm is an integer constant
//     * @param term
//     * @param arg
//     * @return
//     */
//    @Override
//    public List<String> visit(ApplTerm term, Object arg) {
//        List<String> list = new LinkedList<>();
//        FunctionSymbol fs = term.getFunctionSymbol();
//      //  System.out.println(fs.getName() + " " + fs.getArity() + " "+ fs.toString());
//        if(fs.getArity() == 0) {
//            list.add(fs.getName());
//        } else{
//           return defaultVisit(term, arg);
//        }
//        return list;
//    }
//
//}
