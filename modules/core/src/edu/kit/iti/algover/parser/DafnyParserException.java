/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.parser;


/**
 * This error class wraps {@link RecognitionException}s from ANTLR which have a
 * rather poor interface regarding their error messages etc.
 *
 * Unlike most exception classes, this class has mutable objects as knowledge
 * may be added later after creation.
 */
@SuppressWarnings("serial")
public class DafnyParserException extends Exception {

    /**
     * The line number to which the exception is mapped.
     * 0 initially and if no line number known.
     */
    private int line;

    /**
     * The column to which the exception is mapped.
     * 0 initially and if no column number known.
     */
    private int col;


    /**
     * The length of the error region. Most often the length of the erroneous
     * token. Can be 0 for unknown length.
     */
    private int length;

    /**
     * The filename of the file at which the exception was observed. Can be
     * <code>null</code> if no filename available (while parsing interaction
     * e.g.)
     */
    private String filename;

    /**
     * Instantiates a new dafny parser exception.
     *
     * No information is extracted from the cause argument!
     *
     * @param message the message to display
     * @param cause the cause of the exception.
     */
    public DafnyParserException(String message, Throwable cause) {
        super(message, cause);
    }

    /**
     * Instantiates a new dafny parser exception.
     *
     * @param message the message to display
     */
    public DafnyParserException(String message) {
        super(message);
    }

    /**
     * Instantiates a new dafny parser exception.
     *
     * No information is extracted from the cause argument!
     *
     * @param cause the cause of the exception.
     */
    public DafnyParserException(Throwable cause) {
        super(cause);
    }

    /**
     * {@inheritDoc}
     * 
     * <p>
     * This implementation prefixes the message with filename, line number and
     * column number if available. Like
     * <pre>/path/to/file:42:2: Error message</pre>
     */
    @Override
    public String getMessage() {
        StringBuilder sb = new StringBuilder();
        if (filename != null) {
            sb.append(filename);
        }

        if (line > 0) {
            if (sb.length() > 0) {
                sb.append(":");
            }
            sb.append(line);

            if (col > 0) {
                sb.append(":").append(col);
            }
        }

        if (sb.length() > 0) {
            sb.append(": ");
        }

        sb.append(super.getMessage());

        return sb.toString();
    }

    public String getErrorMessage() {
        return super.getMessage();
    }

    public int getLine() {
        return line;
    }

    public void setLine(int line) {
        this.line = line;
    }

    public int getColumn() {
        return col;
    }

    public void setColumn(int col) {
        this.col = col;
    }

    public int getLength() {
        return length;
    }

    public void setLength(int length) {
        this.length = length;
    }

    public void setFilename(String filename) {
        this.filename = filename;
    }

    public String getFilename() {
        return filename;
    }

}
