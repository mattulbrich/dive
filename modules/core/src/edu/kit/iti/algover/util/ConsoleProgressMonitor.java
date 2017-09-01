/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.util;

/**
 * The class can be used in the command line oriented applications to monitor
 * progress on the console.
 *
 * @author Mattias Ulbrich
 */
public class ConsoleProgressMonitor implements ProgressMonitor {

    private double displayed = -1.;
    private final ConsoleProgressMonitor parent;
    private final double factor;
    private final double offset;
    private String msg;

    private ConsoleProgressMonitor(ConsoleProgressMonitor parent, double factor, double offset) {
        this.parent = parent;
        this.factor = factor;
        this.offset = offset;
    }

    public ConsoleProgressMonitor() {
        this.parent = null;
        this.factor = 1.;
        this.offset = 0.;
    }

    @Override
    public void setProgress(double progress) {

        if(parent != null) {
            parent.setProgress(offset + factor * progress);
        }

        if(progress >= displayed+.1 || progress == 1.f) {
            System.out.printf("%s%s %.1f%%%n", Util.duplicate("  ", getDepth()), msg, progress*100);
            displayed = progress;
        }

    }

    private int getDepth() {
        return parent == null ? 0 : parent.getDepth() + 1;
    }

    @Override
    public void setMessage(String msg) {
        this.msg = msg;
    }

    @Override
    public boolean isCancelled() {
        return false;
    }

    @Override
    public ProgressMonitor getSubtaskMonitor(double from, double to) {
        ConsoleProgressMonitor result =
                new ConsoleProgressMonitor(this, from, to-from);
        return result;
    }

}
