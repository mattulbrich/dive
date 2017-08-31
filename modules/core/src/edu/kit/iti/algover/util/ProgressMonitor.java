package edu.kit.iti.algover.util;

/**
 * Interface for indicating the progress of different tasks
 */
public interface ProgressMonitor {

    void setProgress(double amount);

    void setMessage(String msg);

    boolean isCancelled();

    ProgressMonitor getSubtaskListener(int from, int to);

    ProgressMonitor getSubtaskListener(double from, double to);


}
