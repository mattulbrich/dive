///**
// * This file is part of DIVE.
// *
// * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
// */
//package edu.kit.iti.algover.rule.script;
//
//
///**
// * Created by jklamroth on 7/17/18.
// */
//
//// REVIEW: Add the missing generic parameters! Please!
//
//@SuppressWarnings({"unchecked", "rawtypes"})
//public class PrettyPrintVisitor extends DefaultASTVisitor {
//    private String TAB_SYMBOL = "\t";
//    private boolean useWsAsTab = false;
//    private int tabWidth = 4;
//    private int currentTabCount = 0;
//    private String result = "";
//
//    private String getCurrentTabSymbols() {
//        String r = "";
//        for(int i = 0; i < currentTabCount; ++i) {
//            r += TAB_SYMBOL;
//        }
//        return r;
//    }
//
//    @Override
//    public Object defaultVisit(ASTNode node) {
//        return super.defaultVisit(node);
//    }
//
//    @Override
//    public Object visit(ProofScript proofScript) {
//        proofScript.getBody().forEach(statement -> statement.accept(this));
//        return null;
//    }
//
//    @Override
//    public Object visit(CasesStatement casesStatement) {
//        result += getCurrentTabSymbols() + "cases {\n";
//        currentTabCount ++;
//        casesStatement.getCases().forEach(caseStatement -> caseStatement.accept(this));
//        currentTabCount--;
//        result += getCurrentTabSymbols() + "}\n";
//        return null;
//    }
//
//    @Override
//    public Object visit(CaseStatement caseStatement) {
//        result += getCurrentTabSymbols() + caseStatement.toString() + " { \n";
//        currentTabCount++;
//        caseStatement.getBody().forEach(statement -> statement.accept(this));
//        currentTabCount--;
//        result += getCurrentTabSymbols() + "}\n";
//        return null;
//    }
//
//    @Override
//    public Object visit(CallStatement call) {
//        result += getCurrentTabSymbols() + call.toString() + "\n";
//        return null;
//    }
//
//    @Override
//    public Object visit(SimpleCaseStatement simpleCaseStatement) {
//        result += getCurrentTabSymbols() + simpleCaseStatement.toString() + " { \n";
//        currentTabCount++;
//        simpleCaseStatement.getBody().forEach(statement -> statement.accept(this));
//        currentTabCount--;
//        result += getCurrentTabSymbols()+ "}\n";
//        return null;
//    }
//
//    public String getResult() {
//        return result;
//    }
//}
