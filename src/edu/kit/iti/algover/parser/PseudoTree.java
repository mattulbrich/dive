package edu.kit.iti.algover.parser;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import org.antlr.runtime.RecognitionException;
import org.antlr.runtime.Token;
import org.antlr.runtime.TokenStream;
import org.antlr.runtime.tree.CommonTree;
import org.antlr.runtime.tree.CommonTreeAdaptor;
import org.antlr.runtime.tree.Tree;

/**
 * This class implements AST nodes for pseudo code.
 *
 * It extends the existing ANTLR facility {@link CommonTree}. PseudoTrees have
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
public class PseudoTree extends CommonTree {

    /**
     * The Adaptor is used by the {@link PseudoParser} to create PseudoTree
     * instances.
     */
    public static class Adaptor extends CommonTreeAdaptor {

        public Adaptor() {
        }

        @Override
        public Object create(Token payload) {
            return new PseudoTree(payload);
        }

        @Override
        public Object errorNode(TokenStream input, Token start, Token stop,
                RecognitionException e) {
            return new PseudoTree(start);
        }
    }

    /**
     * Instantiates a new pseudo tree.
     *
     * @param payload
     *            the top token defining the type of the node
     */
    public PseudoTree(Token payload) {
        super(payload);
    }

    /**
     * Instantiates a new pseudo tree from an existing one.
     *
     * The array of children is not cloned and remains shared between the trees.
     *
     * @param original
     *            the original tree to clone, not <code>null</code>.
     */
    private PseudoTree(PseudoTree original) {
        super(original);
    }

    /**
     * Instantiates a new, empty pseudo tree. A so-called NIL-Tree
     */
    public PseudoTree() {
        this((Token) null);
    }

    /**
     * Create a node with the same content as this node. This uses the copy
     * constructor {@link #PseudoTree(PseudoTree)}.
     *
     * @return a freshly created PseudoTree instance
     */
    @Override
    public PseudoTree dupNode() {
        PseudoTree result = new PseudoTree(this);
        return result;
    }

    /**
     * Gets the list of children of this node.
     *
     * @return a readonly-view to the list of children of this node,
     *         <code>null</code> if array has not been initialised yet.
     */
    @SuppressWarnings("unchecked")
    public List<PseudoTree> getChildren() {
        if (children == null) {
            return null;
        } else {
            return Collections
                    .unmodifiableList((List<PseudoTree>) (List<?>) children);
        }
    }

    /**
     * Add a child node to this node.
     *
     * @param t
     *            must be of type {@link PseudoTree}.
     */
    @Override
    public void addChild(Tree t) {
        assert t instanceof PseudoTree;
        super.addChild(t);
    }

    /**
     * Returns the first child node that has a given type.
     *
     * @param type
     *            the type of children to look for. Usually an index into
     *            {@link PseudoParser}.
     * @return a child from this node, or <code>null</code>
     */
    @Override
    public PseudoTree getFirstChildWithType(int type) {
        return (PseudoTree) super.getFirstChildWithType(type);
    }

    /**
     * Gets the children that have the given type.
     *
     * @param type
     *            the type of children to look for. Usually an index into
     *            {@link PseudoParser}.
     * @return a freshly created list, modifiable list, possibly empty.
     */
    public List<PseudoTree> getChildrenWithType(int type) {
        List<PseudoTree> result = new ArrayList<PseudoTree>();
        List<PseudoTree> cs = getChildren();
        if (cs != null) {
            for (PseudoTree jmlTree : cs) {
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
     * @return the child at the given index, not <code>null</code>.
     *
     * @throws IndexOutOfBoundsException
     *             if n is not within 0 and {@link #getChildCount()}.
     * @throws NullPointerException
     *             if the children array has not been initialised (but count
     *             would be 0 then, too)
     */
    public PseudoTree getChild(int n) {
        return (PseudoTree) super.getChild(n);
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
    public PseudoTree getLastChild() {
        int childCount = getChildCount();
        if (childCount == 0) {
            return null;
        } else {
            return getChild(childCount - 1);
        }
    }

}
