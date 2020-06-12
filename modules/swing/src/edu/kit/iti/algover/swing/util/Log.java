/*
 * This file is part of
 *    ivil - Interactive Verification on Intermediate Language
 *
 * Copyright (C) 2009-2012 Karlsruhe Institute of Technology
 *
 * The system is protected by the GNU General Public License.
 * See LICENSE.TXT (distributed with this file) for details.
 */
package edu.kit.iti.algover.swing.util;

import java.io.PrintStream;

import edu.kit.iti.algover.util.Util;
import nonnull.NonNull;

/**
 * Log provides static methods for a <b>very basic</b> logging mechanism.
 *
 * <p>
 * This interface can be implemented using various back-ends. A simple console
 * output implementation ({@link SimpleLog}) is included.
 *
 * <p>
 * log4j or java.util.logging can be used if more comfort is desired. An
 * implementation should be easily done.
 * <small>(Look at Log4JLogImplementation in lib)</small>
 *
 * TODO Do the vararg expansion only if the log message is really output.
 *
 * @author mattias ulbrich
 */
public final class Log {

    /**
     * ERROR is a message level indicating a serious failure.
     * <p>
     * In general ERROR messages should describe events that are
     * of considerable importance and which will prevent normal
     * program execution.   They should be reasonably intelligible
     * to end users and to system administrators.
     * This level is initialized to <CODE>50</CODE>.
     */
    public static final int ERROR = 50;

    /**
     * WARNING is a message level indicating a potential problem.
     * <p>
     * In general WARNING messages should describe events that will
     * be of interest to end users or system managers, or which
     * indicate potential problems.
     * This level is initialized to <CODE>40</CODE>.
     */
    public static final int WARNING = 40;

    /**
     * DEBUG is a message level for informational messages.
     * <p>
     * Typically DEBUG messages will be written to the console
     * or its equivalent.  So the INFO level should only be
     * used for reasonably significant messages that will
     * make sense to developers and system admins.
     * This level is initialized to <CODE>30</CODE>.
     */
    public static final int DEBUG = 30;

    /**
     * VERBOSE is a message level providing more deep information.
     * <p>
     * In general the VERBOSE level should be used for information
     * that will be broadly interesting to developers who do not have
     * a specialized interest in the specific subsystem.
     * <p>
     * VERBOSE messages might include things like minor (recoverable)
     * failures.  Issues indicating potential performance problems
     * are also worth logging as VERBOSE.
     * This level is initialized to <CODE>20</CODE>.
     */
    public static final int VERBOSE = 20;

    /**
     * TRACE indicates a highly detailed tracing message.
     * This level is initialized to <CODE>10</CODE>.
     */
    public static final int TRACE = 10;

    /**
     * ALL indicates all messages.
     * This level is initialized to <code>0</code>.
     */
    public static final int ALL = 0;

    /**
     * All actual logging is delegated to an instance of this interface.
     */
    public static interface LogImplementation {

        /**
         * do the actual logging.
         *
         * @param level
         *            the level of the message
         * @param message
         *            the message to be sent to the log system
         */
        void doLog(int level, String message);

        /**
         * do the actual logging for a throwable object.
         *
         * @param level
         *            the level of the message
         * @param e
         *            the throwable to describe on the log system.
         */
        void doStackTrace(int level, Throwable e);

        /**
         * test whether a log level is being log by the system.
         *
         * @param level
         *            the level to test
         * @return true if this level is under surveillance.
         */
        boolean isLogging(int level);

    }

    /**
     * the implementing object to which we delegate our log commands.
     */
    private static LogImplementation logImplementation;

    /**
     * Set up the implementation by system property.
     */
    static {
        // bypass settings!
        String className =
                System.getProperty("dive.log.class", SimpleLog.class.getName());
        try {
            logImplementation = (LogImplementation) Class.forName(className).newInstance();
        } catch (Exception e) {
            System.err.println("Error initialising logging. Disabled!");
            e.printStackTrace();
            logImplementation = null;
        }
    }

    /**
     * Set the {@link LogImplementation} to use for future log output.
     *
     * @param logImplementation
     *            the logImplementation to set
     */
    public static void setLogImplementation(@NonNull LogImplementation logImplementation) {
        Log.logImplementation = logImplementation;
    }

    private Log() {
        // only static methods
    }

    /**
     * Log an message (using {@link Object#toString()}) to {@link System#err}.
     * A line break is automatically amended.
     *
     * Logging level {@link #DEBUG} is used.
     *
     * @see PrintStream#printf(String, Object...)
     * @param format the <code>printf</code> format string
     * @param args arguments to be formatted
     */
    public static void log(String format, Object... args) {
        dbgPrint(DEBUG, String.format(format, args));
    }

    /**
     * Log an message (using {@link Object#toString()}) to {@link System#err}.
     * A line break is automatically amended.
     *
     * Logging level <code>level</code> ist used.
     *
     * @see PrintStream#printf(String, Object...)
     * @param level the level of the log message.
     * @param format the <code>printf</code> format string
     * @param args arguments to be formatted
     */
    public static void log(int level, String format, Object... args) {
        assert level >= 0;
        dbgPrint(level, String.format(format, args));
    }

    /**
     * Log an message (using {@link Object#toString()}) to {@link System#err}.
     * A line break is automatically amended.
     *
     * Logging level <code>level</code> ist used.
     *
     * @param level a non-negative integer indicating the level of log to use
     *
     * @param message the message to log
     */
    public static void log(int level, Object message) {
        assert level >= 0;
        dbgPrint(level, message.toString());
    }

    /**
     * Log a method entry to {@link System#err}.
     *
     * Logging level {@link #TRACE} is used.
     *
     * @param args arguments to the method should be supplied
     */
    public static void enter(Object... args) {
        dbgPrint(TRACE, "enter method \n Arguments: " + Util.join(args, ", "));
    }

    /**
     * Log a method leave to {@link System#err}.
     *
     * Logging level {@link #TRACE} is used.
     */
    public static void leave() {
        dbgPrint(TRACE, "leave method");
    }

    /**
     * print a string to stdout, prefixed by the execution context of the caller
     * of the calling function.
     *
     * If {@link #showOnlyPrefixes} is defined, the output is only written, if
     * the caller prefix begins with one of the specified strings
     *
     * @param string
     *            string to be printed out
     */
    private static void dbgPrint(int level, String string) {
        if(logImplementation != null) {
            logImplementation.doLog(level, string);
        }
    }


    /**
     * Log the stack trace of an exception.
     *
     * The used level is <code>DEBUG</code>.
     *
     * @param e
     *            the throwable object whose trace is to be logged.
     */
    public static void stacktrace(Throwable e) {
        stacktrace(DEBUG, e);

    }

    /**
     * Log the stack trace of an exception.
     *
     * The used level is determined by the argument.
     *
     * @param level
     *            the level to use for the logging.
     *
     * @param e
     *            the throwable object whose trace is to be logged.
     */
    public static void stacktrace(int level, Throwable e) {
        if(logImplementation != null) {
            logImplementation.doStackTrace(level, e);
        }
    }

    /**
     * Check if a log level is being traced at the moment.
     *
     * @param level
     *            level to check
     * @return true iff a message of this level would be published.
     */
    public static boolean isLogging(int level) {
        return logImplementation.isLogging(level);
    }


}