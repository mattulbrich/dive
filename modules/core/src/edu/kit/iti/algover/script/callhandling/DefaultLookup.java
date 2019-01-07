package edu.kit.iti.algover.script.callhandling;


import edu.kit.iti.algover.script.ast.CallStatement;
import edu.kit.iti.algover.script.data.VariableAssignment;
import edu.kit.iti.algover.script.exceptions.NoCallHandlerException;
import edu.kit.iti.algover.script.interpreter.Interpreter;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

/**
 * @author Alexander Weigl
 * @version 1 (20.05.17)
 */

// REVIEW: Add the missing generic parameters! Please!

@SuppressWarnings({"unchecked", "rawtypes"})
public class DefaultLookup implements CommandLookup {

    private final List<CommandHandler> builders = new ArrayList<>(1024);

    public DefaultLookup() {
    }

    public DefaultLookup(CommandHandler... cmdh) {
        builders.addAll(Arrays.asList(cmdh));
    }

    public List<CommandHandler> getBuilders() {
        return builders;
    }

    public void callCommand(Interpreter interpreter,
                            CallStatement call,
                            VariableAssignment params) {
        CommandHandler b = getBuilder(call);
        b.evaluate(interpreter, call, params);
    }


    @Override
    public boolean isAtomic(CallStatement call) {
        try {
            CommandHandler cmdh = getBuilder(call);
            if (cmdh != null)
                return cmdh.isAtomic();
            return true;
        } catch (NoCallHandlerException nche) {
            return false;
        }
    }

    public CommandHandler getBuilder(CallStatement callStatement) {
        CommandHandler found = null;
        for (CommandHandler b : builders) {
            if (b.handles(callStatement)) {
                if (found == null) {
                    found = b;
                } else {
                    throw new IllegalStateException("Call on line"
                            + callStatement.getStartPosition().getLineNumber()
                            + " is ambigue.");
                }
            }
        }

        if (found != null) return found;
        throw new NoCallHandlerException(callStatement);
    }

}
