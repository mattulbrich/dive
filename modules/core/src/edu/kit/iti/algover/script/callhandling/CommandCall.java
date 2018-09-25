package edu.kit.iti.algover.script.callhandling;


import edu.kit.iti.algover.script.interpreter.Interpreter;

/**
 * @author Alexander Weigl
 * @version 1 (20.05.17)
 */
public interface CommandCall<T> {
    void evaluate(Interpreter<T> state);
}
