package edu.kit.iti.algover.parser;

@SuppressWarnings("serial")
public class DafnyException extends Exception {

    private final DafnyTree tree;

    public DafnyException(DafnyTree tree) {
        this.tree = tree;
    }

    public DafnyException(String message, DafnyTree tree, Throwable cause) {
        super(message, cause);
        this.tree = tree;
    }

    public DafnyException(String message, DafnyTree tree) {
        super(message);
        this.tree = tree;
    }

    public DafnyException(DafnyTree tree, Throwable cause) {
        super(cause);
        this.tree = tree;
    }

    public DafnyTree getTree() {
        return tree;
    }

}
