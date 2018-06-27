package edu.kit.iti.algover.smttrans.access;

public class SolverParameter {

    private String smt;
    private int timeout;
    private boolean log;

    
    public SolverParameter (String smt) {
        this.smt = smt;
        this.timeout = 3;
        this.log = false;
    }
    
    public SolverParameter(String smt, int timeout,boolean log) {
        this.log = log;
        this.timeout = timeout;
        this.smt = smt;
    }
    
    public SolverParameter(String smt, int timeout) {
        this.log = false;
        this.timeout = timeout;
        this.smt = smt;
    }
    

    public SolverParameter(String smt, boolean log) {
        this.log = log;
        this.timeout = 3;
        this.smt = smt;
    }
    public String getSMT() {
        return smt;
    }

    public int getTimeout() {
        return timeout;
    }

    public boolean getlog() {
        return log;
    }

}
