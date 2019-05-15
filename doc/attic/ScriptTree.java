package edu.kit.iti.algover.script;

import org.antlr.runtime.CommonToken;
import org.antlr.runtime.RecognitionException;
import org.antlr.runtime.Token;
import org.antlr.runtime.TokenStream;
import org.antlr.runtime.tree.CommonTree;
import org.antlr.runtime.tree.CommonTreeAdaptor;
import org.antlr.runtime.tree.Tree;


import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

/**
 * Created by sarah on 8/16/16.
 */
public class ScriptTree extends CommonTree {
    public static class Adaptor extends CommonTreeAdaptor{
        public Adaptor() {
        }

        @Override
        public Object create(Token payload) {
            return new ScriptTree(payload);
        }

        @Override
        public Object errorNode(TokenStream input, Token start, Token stop,
                                RecognitionException e) {
            return new ScriptTree(start);
        }
    }
    private ScriptTree declaration;

    /**
     * Instantiates a new Script tree.
     *
     * @param payload
     *            the top token defining the type of the node
     */
    public ScriptTree(Token payload) {
        super(payload);
    }

    /**
     * Instantiates a new Script tree from an existing one.
     *
     * The array of children is not cloned and remains shared between the trees.
     *
     * @param original
     *            the original tree to clone, not <code>null</code>.
     */
    private ScriptTree(ScriptTree original) {
        super(original);
    }

    /**
     * Instantiates a new, empty Script tree. A so-called NIL-Tree
     */
    public ScriptTree() {
        this((Token) null);
    }

    /**
     * Instantiates a new Script tree. A new (virtual) token is created from the
     * arguments.
     *
     * @see ScriptParser
     *
     * @param type
     *            type of the token, see contants of {@link ScriptParser}.
     * @param image
     *            the string to embed
     */
    public ScriptTree(int type, String image) {
        this(new CommonToken(type, image));
    }

    /**
     * Instantiates a new Script tree. A new (virtual) token is created from the
     * argument.
     *
     * @see ScriptParser
     *
     * @param type
     *            type of the token, see contants of {@link ScriptParser}.
     */
    public ScriptTree(int type) {
        this(new CommonToken(type));
    }

    /**
     * Create a node with the same content as this node. This uses the copy
     * constructor {@link #ScriptTree(ScriptTree)}.
     *
     * @return a freshly created ScriptTree instance
     */
    @Override
    public ScriptTree dupNode() {
        ScriptTree result = new ScriptTree(this);
        return result;
    }

    /**
     * Gets the list of children of this node.
     *
     * @return a readonly-view to the list of children of this node,
     *         <code>null</code> if array has not been initialised yet.
     */
    //@SuppressWarnings("unchecked")
    public List<ScriptTree> getChildren() {
        if (children == null) {
            return null;
        } else {
            return Collections
                    .unmodifiableList(children);
        }
    }

    /**
     * Add a child node to this node.
     *
     * @param t
     *            must be of type {@link ScriptTree}.
     */

    public void addChild(Tree t) {
        assert t instanceof ScriptTree;
        super.addChild(t);
    }

    /**
     * Returns the first child node that has a given type.
     *
     * @param type
     *            the type of children to look for. Usually an index into
     *            {@link ScriptParser}.
     * @return a child from this node, or <code>null</code>
     */
    @Override
    public ScriptTree getFirstChildWithType(int type) {
        return (ScriptTree) super.getFirstChildWithType(type);
    }

    /**
     * Gets the children that have the given type.
     *
     * @param type
     *            the type of children to look for. Usually an index into
     *            {@link ScriptParser}.
     * @return a freshly created list, modifiable list, possibly empty.
     */
    public List<ScriptTree> getChildrenWithType(int type) {
        List<ScriptTree> result = new ArrayList<ScriptTree>();
        List<ScriptTree> cs = getChildren();
        if (cs != null) {
            for (ScriptTree jmlTree : cs) {
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
    public ScriptTree getChild(int n) {
        return (ScriptTree) super.getChild(n);
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
    public ScriptTree getLastChild() {
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
            string = ScriptParser.tokenNames[token.getType()];
        }
        return string;
    }
/*
    *//**
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
     *//*
    public <R, A> R accept(ScriptTreeVisitor<R, A> visitor, A arg) {
        return ScriptDispatch.dispatch(visitor, this, arg);
    }*/

}
