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

public class SimpleLog implements Log.LogImplementation {

    /**
     * The minimum level of a log message to be displayed.
     * 
     * We cannot use Settings here because that leads to a loop -
     * Settings uses Log and always prints a message.
     */
    private int minLevel = Integer.getInteger("dive.log", Log.DEBUG);
    
    public SimpleLog() {
    }
    
    public SimpleLog(int minLevel) {
        this();
        setMinLevel(minLevel);
    }

    
    public int getMinLevel() {
        return minLevel;
    }


    public void setMinLevel(int level) {
        assert level >= 0;
        minLevel = level;
    }
    
    @Override
    public void doLog(int level, String string) {
        if(level >= minLevel) {
            String prefix = getClassAndMethod(4);
            String threadName = Thread.currentThread().getName();
            System.err.println("> " + prefix + " [" + threadName + 
                    "] - Level " + levelToString(level) + "\n  " + string);
        }
    }

    @Override
    public void doStackTrace(int level, Throwable e) {
        if(level >= minLevel) {
            String prefix = getClassAndMethod(4);
            System.err.println("> EXCEPTION in " + prefix + ":");
            e.printStackTrace(System.err);
        }
    }
    
    /*
     * return information about some execution context. The context of interest
     * may have appeared several levels higher.
     * 
     * @author MU
     * @param level
     *            to go up in the context hierarchy
     * @return a String giving information about the stack of the calling
     *         function.
     */
    private static String getClassAndMethod(int level) {
        StackTraceElement[] trace = new Exception().getStackTrace();
        if (trace.length > level) {
            return trace[level].toString();
        }
        return "";
    }
    
    /*
     * get the readable counterpart for an integer log level
     */
    private static String levelToString(int level) {
        switch(level) {
        case 50: return "ERROR";
        case 40: return "WARNING";
        case 30: return "DEBUG";
        case 20: return "VERBOSE";
        case 10: return "TRACE";
        }
        return Integer.toString(level);
    }
    
    
    // testing only
    public static void main(String[] args) {
        
        SimpleLog simpImpl = new SimpleLog();
        Log.setLogImplementation(simpImpl);
        
        simpImpl.setMinLevel(Log.TRACE);
        Log.enter((Object)args);
        
        simpImpl.setMinLevel(Log.DEBUG);
        // should not do anything
        Log.leave();
        Log.log(Log.VERBOSE, "VERBOSE: Should not be printed");
        Log.log(Log.DEBUG, "DEBUG: Should be printed");
        Log.log(Log.WARNING, "WARNING: Should be printed");
        Log.log(Log.ERROR, "ERROR: Should be printed");
        Log.log(88, "88: Should be printed");
        
        try {
            throw new Exception("Hello World");
        } catch (Exception e) {
            Log.stacktrace(e);
        }
        
        simpImpl.setMinLevel(Log.TRACE);
        Log.leave();
    }


    @Override
    public boolean isLogging(int level) {
        return minLevel <= level;
    }

}
