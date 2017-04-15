/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2016 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.parser;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import org.antlr.runtime.CommonToken;
import org.antlr.runtime.RecognitionException;
import org.antlr.runtime.Token;
import org.antlr.runtime.TokenStream;
import org.antlr.runtime.tree.CommonTree;
import org.antlr.runtime.tree.CommonTreeAdaptor;
import org.antlr.runtime.tree.Tree;


/**
 * This class implements AST nodes for Dafny code.
 *
 * It extends the existing ANTLR facility {@link CommonTree}. DafnyTrees have
 * got a head token ({@link CommonTree#token}) that determines its type, and
 * children.
 *
 * Important resources for accessing AST nodes:
 * <ul>
 * <li>{@link CommonTree#token} to access the type defining token.
 * <li>{@link #getChildren()}, {@link #getChild(int)}, {@link #getChildCount()}
 * to access the children.
 * <li>{@link #getFirstChildWithType(int)}, {@link #getChildrenWithType(int)} to
 * filter the list of children.
 *
 * @author Mattias Ulbrich
 */
public class DafnyTree extends CommonTree {



    /**
     * The Adaptor is used by the {@link DafnyParser} to create DafnyTree
     * instances.
     */
    public static class Adaptor extends CommonTreeAdaptor {

        public Adaptor() {
        }

        @Override
        public Object create(Token payload) {
            return new DafnyTree(payload);
        }

        @Override
        public Object errorNode(TokenStream input, Token start, Token stop,
                RecognitionException e) {
            return new DafnyTree(start);
        }
    }

    // TODO For the future
    // MU: ???
    // private DafnyTree declaration;

    /**
     * Instantiates a new Dafny tree.
     *
     * @param payload
     *            the top token defining the type of the node
     */
    public DafnyTree(Token payload) {
        super(payload);
    }

    /**
     * Instantiates a new Dafny tree from an existing one.
     *
     * The array of children is not cloned and remains shared between the trees.
     *
     * @param original
     *            the original tree to clone, not <code>null</code>.
     */
    private DafnyTree(DafnyTree original) {
        super(original);
    }

    /**
     * Instantiates a new, empty Dafny tree. A so-called NIL-Tree
     */
    public DafnyTree() {
        this((Token) null);
    }

    /**
     * Instantiates a new Dafny tree. A new (virtual) token is created from the
     * arguments.
     *
     * @see DafnyParser
     *
     * @param type
     *            type of the token, see contants of {@link DafnyParser}.
     * @param image
     *            the string to embed
     */
    public DafnyTree(int type, String image) {
        this(new CommonToken(type, image));
    }

    /**
     * Instantiates a new Dafny tree. A new (virtual) token is created from the
     * argument.
     *
     * @see DafnyParser
     *
     * @param type
     *            type of the token, see contants of {@link DafnyParser}.
     */
    public DafnyTree(int type) {
        this(new CommonToken(type));
    }

    /**
     * Create a node with the same content as this node. This uses the copy
     * constructor {@link #DafnyTree(DafnyTree)}.
     *
     * @return a freshly created DafnyTree instance
     */
    @Override
    public DafnyTree dupNode() {
        DafnyTree result = new DafnyTree(this);
        return result;
    }

    /**
     * Gets the list of children of this node.
     *
     * @return a readonly-view to the list of children of this node,
     *         <code>null</code> if array has not been initialised yet.
     */
    @SuppressWarnings("unchecked")
    public List<DafnyTree> getChildren() {
        if (children == null) {
            return null;
        } else {
            return Collections
                    .unmodifiableList((List<DafnyTree>) (List<?>) children);
        }
    }

    /**
     * Add a child node to this node.
     *
     * @param t
     *            must be of type {@link DafnyTree}.
     */
    @Override
    public void addChild(Tree t) {
        assert t instanceof DafnyTree;
        super.addChild(t);
    }

    /**
     * Returns the first child node that has a given type.
     *
     * @param type
     *            the type of children to look for. Usually an index into
     *            {@link DafnyParser}.
     * @return a child from this node, or <code>null</code>
     */
    @Override
    public DafnyTree getFirstChildWithType(int type) {
        return (DafnyTree) super.getFirstChildWithType(type);
    }

    /**
     * Gets the children that have the given type.
     *
     * @param type
     *            the type of children to look for. Usually an index into
     *            {@link DafnyParser}.
     * @return a freshly created list, modifiable list, possibly empty.
     */
    public List<DafnyTree> getChildrenWithType(int type) {
        List<DafnyTree> result = new ArrayList<DafnyTree>();
        List<DafnyTree> cs = getChildren();
        if (cs != null) {
            for (DafnyTree jmlTree : cs) {
                if (jmlTree.getType() == type) {
                    result.add(jmlTree);
                }
            }
        }
        return result;
    }

    /**
     * Gets the child at a given index.
     *
     * @param n the index of the child, must be in bounds.
     *
     * @return the child at the given index, not <code>null</code>.
     *
     * @throws IndexOutOfBoundsException
     *             if n is not within 0 and {@link #getChildCount()}.
     * @throws NullPointerException
     *             if the children array has not been initialised (but count
     *             would be 0 then, too)
     */
    public DafnyTree getChild(int n) {
        return (DafnyTree) super.getChild(n);
    }

    /**
     * Gets the number of children in this node.
     *
     * @return the number of children in this node, 0 if no children array
     *         created.
     */
    @Override
    public int getChildCount() {
        if (children == null) {
            return 0;
        } else {
            return children.size();
        }
    }

    /**
     * Gets the last child of the node.
     *
     * @return the last child of the node, <code>null</code> if there are no
     *         children.
     */
    public DafnyTree getLastChild() {
        int childCount = getChildCount();
        if (childCount == 0) {
            return null;
        } else {
            return getChild(childCount - 1);
        }
    }

    @Override
    public String toString() {
        String string = super.toString();
        if (string == null && token != null) {
            string = DafnyParser.tokenNames[token.getType()];
        }
        return string;
    }

    /**
     * Accept a visitor according to the visitor pattern.
     *
     * Dynamic dispatch is over the type of the
     *
     * @param <R>
     *            the generic return type of the visitor
     * @param <A>
     *            the generic argument type of the visitor
     * @param visitor
     *            the non-<code>null</code> visitor to go over
     * @param arg
     *            the argument to provide
     * @return the result by the visitor.
     */
    public <R, A> R accept(DafnyTreeVisitor<R, A> visitor, A arg) {
        return DafnyDispatch.dispatch(visitor, this, arg);
    }

}
