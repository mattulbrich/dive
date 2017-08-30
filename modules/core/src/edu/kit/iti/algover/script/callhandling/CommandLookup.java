package edu.kit.iti.algover.script.callhandling;


import edu.kit.iti.algover.script.ast.CallStatement;
import edu.kit.iti.algover.script.data.VariableAssignment;
import edu.kit.iti.algover.script.interpreter.Interpreter;

/**
 * @author Alexander Weigl
 * @version 1 (20.05.17)
 */
public interface CommandLookup<T> {
    void callCommand(Interpreter<T> i, CallStatement c, VariableAssignment p);

    boolean isAtomic(CallStatement call);

    public CommandHandler getBuilder(CallStatement callStatement);
}
