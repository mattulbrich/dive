package edu.kit.iti.algover.proof;

/**
 * The illegalstateexepction should be thron by all methdos, performing a symbolic execution wiothout
 * parsing the method before
 * Created by sarah on 10/26/15.
 */

// REVIEW: It does not seem to be used. Remove?
// REVIEW: Exception class is not used.

public class IllegalStateException extends Exception{
    public IllegalStateException(String message){
        super(message);
        System.out.println("The problem file has to be parsed in order to perform this operation. "+message);
    }

}
