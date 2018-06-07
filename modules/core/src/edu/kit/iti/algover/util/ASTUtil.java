/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.util;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.NoSuchElementException;
import java.util.Set;

import edu.kit.iti.algover.term.builder.TermBuilder;
import org.antlr.runtime.tree.Tree;

import edu.kit.iti.algover.parser.DafnyParser;
import edu.kit.iti.algover.parser.DafnyTree;
import edu.kit.iti.algover.symbex.LocalVarDecl;
import edu.kit.iti.algover.symbex.SymbexPath;
import edu.kit.iti.algover.term.Sort;
import nonnull.NonNull;

/**
 * The class ASTUtil is a collection of static method for operation on DafnyTrees.
 *
 * @see DafnyTree
 *
 * @author Mattias Ulbrich
 */
public final class ASTUtil {

    private ASTUtil() {
        throw new Error();
    }

    public static DafnyTree create(int type, DafnyTree... children) {
        DafnyTree result = new DafnyTree(type);
        for (DafnyTree child : children) {
            result.addChild(child);
        }
        return result;
    }

    /**
     * Creates an AST for the negation of a formula.
     *
     * @param cond the AST for a formula
     * @return the AST for the negated formula.
     */
    public static DafnyTree negate(DafnyTree cond) {
        DafnyTree result = new DafnyTree(DafnyParser.NOT, "not");
        result.addChild(cond);
        return result;
    }

    /**
     * Gets the label for the proof obligation in this object.
     *
     * @param tree
     *            a non-<code>null</code> ast node
     * @return the label, could be <code>null</code>
     */
    public static String getLabel(DafnyTree tree) {
        DafnyTree label = tree.getFirstChildWithType(DafnyParser.LABEL);
        if (label != null) {
            return label.getLastChild().toString();
        }
        return null;
    }

    /**
     * Returns a constant tree for the <code>null</code> literal.
     *
     * @return a freshly created tree
     */
    // Checkstyle: IGNORE MethodNameCheck
    public static DafnyTree _null() {
        return new DafnyTree(DafnyParser.NULL, "null");
    }


    /**
     * Returns a new constant tree for the <code>this</code> literal.
     *
     * @return a freshly created tree
     */
    // Checkstyle: IGNORE MethodNameCheck
    public static DafnyTree _this() {
        return new DafnyTree(DafnyParser.THIS, "this");
    }


    /**
     * Returns a tree for an equality on asts.
     *
     * @param tree1 the lhs of the equality, not <code>null</code>
     * @param tree2 the rhs of the equality, not <code>null</code>
     * @return a freshly created tree
     */
    public static DafnyTree equals(DafnyTree tree1, DafnyTree tree2) {
        DafnyTree result = new DafnyTree(DafnyParser.EQ, "=");
        result.addChild(tree1);
        result.addChild(tree2);
        return result;
    }

    /**
     * Returns a tree for a "Not equals" expression.
     *
     * @param tree1 the lhs of the inequality, not <code>null</code>
     * @param tree2 the rhs of the inequality, not <code>null</code>
     * @return a freshly created dafny tree
     */
    public static DafnyTree notEquals(DafnyTree tree1, DafnyTree tree2) {
        DafnyTree result = new DafnyTree(DafnyParser.NEQ, "!=");
        result.addChild(tree1);
        result.addChild(tree2);
        return result;
    }

    /**
     * Returns a tree for a conjunction on ast trees.
     *
     * @param conj1 the first conjunct, not <code>null</code>
     * @param conj2 the second conjunct, not <code>null</code>
     * @return a freshly created dafny tree
     */
    public static DafnyTree and(DafnyTree conj1, DafnyTree conj2) {
        DafnyTree result = new DafnyTree(DafnyParser.AND, "&&");
        result.addChild(conj1);
        result.addChild(conj2);
        return result;
    }

    /**
     * Returns a tree for a conjunction with arbitrary many conjuncts.
     *
     * The result is associated to the left, e.g., <code>and(a,b,c)</code>
     * results in <code>(&& (&& a b) c)</code>.
     *
     * If the collection is a singleton, the sole argument is returned.
     *
     * @throws IllegalArgumentException
     *             if {@code trees} is empty
     * @param trees
     *            a non-<code>null</code> collection of conjuncts
     * @return a possibly freshy created dafny tree
     */
    public static DafnyTree and(Iterable<DafnyTree> trees) {

        DafnyTree result = new DafnyTree(DafnyParser.AND, "&&");
        for (DafnyTree tree : trees) {
            if (result.getChildCount() == 2) {
                DafnyTree t = new DafnyTree(DafnyParser.AND, "&&");
                t.addChild(result);
                result = t;
            }
            result.addChild(tree);
        }

        if (result.getChildCount() == 0) {
            throw new IllegalArgumentException("Empty conjunction not supported");
        }

        if (result.getChildCount() == 1) {
            result = result.getChild(0);
        }

        return result;
    }

    /**
     * Returns an implication of DafnyTrees.
     *
     * @param premiss
     *            the ast for the premiss, not <code>null</code>
     * @param concl
     *            the ast for the conclusion, not <code>null</code>
     * @return a freshly created dafny tree
     */
    public static DafnyTree impl(DafnyTree premiss, DafnyTree concl) {
        DafnyTree result = new DafnyTree(DafnyParser.IMPLIES, "==>");
        result.addChild(premiss);
        result.addChild(concl);
        return result;
    }

    /**
     * Returns a tree for an integer literal.
     *
     * @param value
     *            the value of the literal
     * @return a freshly created dafny tree
     */
    public static DafnyTree intLiteral(int value) {
        DafnyTree result = new DafnyTree(DafnyParser.INT_LIT, Integer.toString(value));
        return result;
    }

    /**
     * Returns a tree for a ">=" comparison.
     *
     * @param exp1 the first expression, not <code>null</code>
     * @param exp2 the second expression, not <code>null</code>
     * @return a freshly created dafny tree
     */
    public static DafnyTree greaterEqual(DafnyTree exp1, DafnyTree exp2) {
        DafnyTree result = new DafnyTree(DafnyParser.GE, ">=");
        result.addChild(exp1);
        result.addChild(exp2);
        return result;
    }

    /**
     * Returns a tree for a "<=" comparison.
     *
     * @param exp1 the first expression, not <code>null</code>
     * @param exp2 the second expression, not <code>null</code>
     * @return a freshly created dafny tree
     */
    public static DafnyTree lessEqual(DafnyTree exp1, DafnyTree exp2) {
        DafnyTree result = new DafnyTree(DafnyParser.LE, "<=");
        result.addChild(exp1);
        result.addChild(exp2);
        return result;
    }

    /**
     * Returns a tree for a "<" comparison.
     *
     * @param exp1 the first expression, not <code>null</code>
     * @param exp2 the second expression, not <code>null</code>
     * @return a freshly created dafny tree
     */
    public static DafnyTree less(DafnyTree exp1, DafnyTree exp2) {
        DafnyTree result = new DafnyTree(DafnyParser.LT, "<");
        result.addChild(exp1);
        result.addChild(exp2);
        return result;
    }

    /**
     * Returns a tree for a Noetherian termination comparison.
     *
     * @param exp1 the first expression, not <code>null</code>
     * @param exp2 the second expression, not <code>null</code>
     * @return a freshly created dafny tree
     */
    public static DafnyTree noetherLess(DafnyTree exp1, DafnyTree exp2) {
        DafnyTree result = new DafnyTree(DafnyParser.NOETHER_LESS);
        result.addChild(exp1);
        result.addChild(exp2);
        return result;
    }

    /**
     * Returns a tree for the length of an single-dim array.
     *
     * @param array the reference whose length is to be taken, not <code>null</code>
     * @return a freshly created dafny tree
     */
    public static DafnyTree length(DafnyTree array) {
        DafnyTree result = new DafnyTree(DafnyParser.LENGTH, "Length");
        result.addChild(array);
        return result;
    }

    /**
     * Returns an identifier token with the given variable/id name.
     *
     * @param id non-<code>null</code> name of identifier
     * @return a freshly created dafny tree
     */
    public static DafnyTree id(String id) {
        return new DafnyTree(DafnyParser.ID, id);
    }

    /**
     * Returns an identifier token with the given variable/id name.
     *
     * @param name non-<code>null</code> name of identifier
     * @param ref a tree to point to as declaration reference
     * @return a freshly created dafny tree
     */
    public static DafnyTree id(String name, DafnyTree ref) {
        DafnyTree id = id(name);
        id.setDeclarationReference(ref);
        return id;
    }

    public static DafnyTree var(String name, Iterable<LocalVarDecl> immutableList) {
        for (LocalVarDecl loc : immutableList) {
            if (loc.getName().equals(name)) {
                DafnyTree id = id(name);
                id.setDeclarationReference(loc.getReference());
                return id;
            }
        }

        throw new NoSuchElementException("Variable " + name + " not defined.");
    }

    public static DafnyTree builtInVar(String name) {
        DafnyTree builtin = new DafnyTree(DafnyParser.VAR, "builtin");
        DafnyTree result = new DafnyTree(DafnyParser.ID, name);
        result.setDeclarationReference(builtin);
        return result;
    }

    public static DafnyTree anonymise(DafnyTree varDecl) {
        DafnyTree id = id(varDecl.getChild(0).getText());
        id.setDeclarationReference(varDecl);
        DafnyTree type = varDecl.getFirstChildWithType(DafnyParser.TYPE).getChild(0);
        id.setExpressionType(type);
        DafnyTree wildcard = new DafnyTree(DafnyParser.WILDCARD);
        wildcard.setExpressionType(type);
        return create(DafnyParser.ASSIGN, id, wildcard);
    }

    public static DafnyTree anonymiseHeap(SymbexPath path, DafnyTree mod) {
        DafnyTree heap = builtInVar("$heap");
        DafnyTree anonHeap = freshVariable("$aheap", id("heap"), path);
        DafnyTree anon = call("$anon", heap, mod, anonHeap);
        return assign(heap, anon);
    }

    public static DafnyTree anonymiseHeap(SymbexPath path) {
        return anonymiseHeap(path, builtInVar("$mod"));
    }

    public static DafnyTree call(String function, DafnyTree... args) {
        DafnyTree argsTree = create(DafnyParser.ARGS, args);
        DafnyTree id = id(function);
        return create(DafnyParser.CALL, id, argsTree);
    }

    public static DafnyTree assign(@NonNull DafnyTree var, @NonNull DafnyTree value) {
        return create(DafnyParser.ASSIGN, var, value);
    }

    /**
     * Returns a variable declaration tree node.
     *
     * The id and type for the declaration must be given
     *
     * @param id the non-<code>null</code> id of the declaration
     * @param type the non-<code>null</code> type
     * @return a freshly created Dafny tree
     */
    public static DafnyTree varDecl(DafnyTree id, DafnyTree type) {
        DafnyTree result = new DafnyTree(DafnyParser.VAR);
        result.addChild(id);
        result.addChild(type);
        return result;
    }

    public static DafnyTree freshVariable(String base, DafnyTree type, SymbexPath path) {

        Set<String> names = new HashSet<>();
        for (LocalVarDecl tree : path.getDeclaredLocalVars()) {
            names.add(tree.getName());
        }

        int count = 1;
        String name = base + "_" + count;
        while (names.contains(name)) {
            count++;
            name = base + "_" + count;
        }

        DafnyTree decl = varDecl(id(name), type);
        DafnyTree result = id(name);
        result.setDeclarationReference(decl);
        path.addDeclaredLocalVar(new LocalVarDecl(name, type, decl));

        return result;
    }

    /*
     * Put decreases list into a list expression
     */
    public static DafnyTree listExpr(List<DafnyTree> entries) {
        DafnyTree result = new DafnyTree(DafnyParser.LISTEX);
        result.addChildren(entries);
        return result;
    }

    public static DafnyTree _false() {
        return new DafnyTree(DafnyParser.FALSE, "false");
    }

    public static String getFieldConstantName(DafnyTree reference) {
        assert reference.getType() == DafnyParser.FIELD;

        Tree clss = reference.parent;
        assert clss.getType() == DafnyParser.CLASS;

        String clssName = clss.getChild(0).getText();
        String fieldName = reference.getChild(0).getText();

        return TermBuilder.fieldName(clssName, fieldName);
    }

    public static Sort toSort(DafnyTree tree) {
        if(tree.getChildCount() == 0) {
            return Sort.get(tree.getText());
        } else {
            Sort[] args = new Sort[tree.getChildCount()];
            for (int i = 0; i < args.length; i++) {
                args[i] = toSort(tree.getChild(i));
            }
            return Sort.get(tree.getText(), args);
        }
    }

    public static DafnyTree type(String type) {
        return create(DafnyParser.TYPE, id(type));
    }

    public static DafnyTree letCascade(List<Pair<String, DafnyTree>> subs, DafnyTree expression) {

        DafnyTree result = new DafnyTree(DafnyParser.LET);
        DafnyTree vars = new DafnyTree(DafnyParser.VAR);
        result.addChild(vars);
        for (Pair<String, DafnyTree> sub : subs) {
            vars.addChild(id(sub.fst));
            result.addChild(sub.snd);
        }
        result.addChild(expression);
        return result;

    }

    public static Collection<Pair<String, DafnyTree>> methodParameterSubs(DafnyTree method, DafnyTree args) {
        List<Pair<String, DafnyTree>> result = new ArrayList<>();
        DafnyTree formalParams = method.getFirstChildWithType(DafnyParser.ARGS);
        assert formalParams.getChildCount() == args.getChildCount();

        for (int i = 0; i < args.getChildCount(); i++) {
            result.add(new Pair<>(formalParams.getChild(i).getChild(0).getText(), args.getChild(i)));
        }

        return result;
    }

    public static DafnyTree inMod(DafnyTree receiver) {
        DafnyTree result = new DafnyTree(DafnyParser.IN);
        result.addChild(receiver.dupTree());
        result.addChild(builtInVar("$mod"));
        return result;
    }
}
