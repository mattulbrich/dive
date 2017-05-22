/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.dafnystructures;

import java.util.List;

import edu.kit.iti.algover.parser.DafnyTree;

/**
 * Class representing a single Dafnyfunction
 * A function has zero or n arguments, a return type, zero or more contracts and a body
 */
public class DafnyFunction extends DafnyDecl{

    private final List<DafnyTree> params;
    private final List<DafnyTree> requiresClauses;
    private final List<DafnyTree> ensuresClauses;
    private final DafnyTree decreasesClause;
    private final DafnyTree expression;

    public DafnyFunction(DafnyFunctionBuilder b) {
        super(b.getFilename(), b.getRepresentation(), b.getName(), b.isInLibrary());
        this.params = b.getParameters();
        this.ensuresClauses = b.getEnsuresClauses();
        this.requiresClauses = b.getRequiresClauses();
        this.expression = b.getExpression();
        this.decreasesClause = b.getDecreasesClause();
    }
    /**
     * The return type of the function. Non-null
     */
    private DafnyTree returnType;

    public List<DafnyTree> getParameters() {
        return params;
    }

    public DafnyTree getReturnType() {
        return returnType;
    }

    public DafnyTree getExpression() {
        return expression;
    }

    public String toString(){
        String s = "function "+this.getName()+"\n";

        if(this.getParameters() != null){
            String params = this.getParameters().size()+" Parameters: ";

            for (DafnyTree para:this.getParameters()) {
                params+=para.toStringTree()+"\n";
            }
            s+=params+"\n";
        }
//        s += "returns "+this.returnType.toStringTree()+"\n";
//        s += "with body \n"+this.body.toStringTree();

        return s;
    }
    @Override
    public <R, A> R accept(DafnyDeclVisitor<R,A> visitor, A arg) {
        return visitor.visit(this, arg);
    }
}
