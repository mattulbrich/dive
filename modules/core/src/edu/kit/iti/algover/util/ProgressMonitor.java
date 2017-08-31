/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.util;

import nonnull.NonNull;

/**
 * Interface for allowing the algorithms to indicate the progress a task to the
 * UI.
 *
 * Do not use <code>null</code> if no monitoring should happen. Instead use
 * {@link #NO_MONITOR}.
 */
public interface ProgressMonitor {

    static ProgressMonitor NO_MONITOR = new ProgressMonitor() {
        @Override public void setProgress(double progress) { }
        @Override public void setMessage(String msg) { }
        @Override public boolean isCancelled() { return false; }
        @Override public ProgressMonitor getSubtaskMonitor(double from, double to) { return this; }
    };

    /**
     * Updates the progress of the process.
     *
     * The progress is modelled as a floating point value between 0 and 1.
     *
     * Call must not decrease previously set progress. The sequence of method
     * calls must be monotonic.
     *
     * @param progress
     *            a value between such that {@code 0 <= progress <= 1.};
     */
    void setProgress(double progress);

    /**
     * Update the message which is displayed to the user during while waiting.
     *
     * @param msg the new message
     */
    void setMessage(@NonNull String msg);

    /**
     * Checks if the user requested cancelling the task.
     *
     * There may be a key code oder button to cancel a task.
     *
     * @return <code>true</code> iff has been cancelled
     */
    boolean isCancelled();

    /**
     * Create a monitor which can be used to model a subrange of the task
     * interval.
     *
     * The from value is mapped to 0 of the result, the end point is mapped to 1
     * of the result.
     *
     * @param from
     *            the starting point where the monitor should start.
     * @param to
     *            the end point where the monitor should end
     *
     * @return the monitor for the subtask
     *
     * @see #getSubtaskMonitor(int, int)
     */
    @NonNull ProgressMonitor getSubtaskMonitor(double from, double to);

    /**
     * Create a monitor which can be used to model a subrange of the task
     * interval.
     *
     * The range is computed from the index of the task amongst a list of tasks
     * with equally distributed porgress.
     *
     * @param index
     *            the number of the subtask amongst all of them.
     * @param to
     *            the total number of all subtasks.
     *
     * @return the monitor for the subtask
     *
     * @see #getSubtaskMonitor(int, int)
     */
    default @NonNull ProgressMonitor getSubtaskMonitor(int index, int total) {
        double doubleTotal = (double)total;
        return getSubtaskMonitor(index / doubleTotal, (index+1) / doubleTotal);
    }

}
