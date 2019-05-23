/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
/*
 * This file is part of
 *    ivil - Interactive Verification on Intermediate Language
 *
 * Copyright (C) 2009-2012 Karlsruhe Institute of Technology
 *
 * The system is protected by the GNU General Public License.
 * See LICENSE.TXT (distributed with this file) for details.
 */
package edu.kit.iti.algover.util;

/**
 * A format exception is thrown if a string is ill-formatted and can hence not
 * be processed.
 *
 * <p>
 * It could be used by a variety of read from string methods as well and then
 * should be moved.
 *
 * @see TermSelector
 * @see SubtermSelector
 */
public class FormatException extends Exception {

    private static final long serialVersionUID = 7438807629735716687L;
    private String kind;
    private String msg;
    private String content;

    /**
     * Instantiates a new format exception.
     *
     * <p>The resulting error message is equal to:
     * <pre>
     *   "Error in " + kind + ": " + msg + "\nIn: " + content
     * </pre>
     *
     * @param kind
     *            the kind of the processing that should have taken place
     * @param msg
     *            the error message
     * @param content
     *            the erroneous content
     */
    public FormatException(String kind, String msg, String content) {
        this.kind = kind;
        this.msg = msg;
        this.content = content;
    }

    public String getMessage() {
        return "Error in " + kind + ": " + msg + "\nIn: " + content;
    }

}
