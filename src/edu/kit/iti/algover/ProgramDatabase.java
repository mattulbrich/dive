package edu.kit.iti.algover;

import edu.kit.iti.algover.parser.DafnyParser;
import edu.kit.iti.algover.parser.DafnyTree;


/**
 * The Class ProgramDatabase serves as database for all information on the
 * program: Defined functions, contracts, declared variables.
 *
 * At the moment, everything is parsed from the AST on demand.
 */
public class ProgramDatabase {

    private final DafnyTree program;

    public ProgramDatabase(DafnyTree program) {
        this.program = program;
    }

    public DafnyTree getFunction(String name) {
        for (DafnyTree f : program.getChildrenWithType(DafnyParser.METHOD)) {
            if(f.getChild(0).getText().equals(name)) {
                return f;
            }
        }
        return null;
    }

    public DafnyTree getVariableDeclaration(DafnyTree function, String name) {
        DafnyTree arg = getVariableDeclInList(function.getFirstChildWithType(DafnyParser.ARGS), name);
        if(arg != null) {
            return arg;
        }

        DafnyTree ret = getVariableDeclInList(function.getFirstChildWithType(DafnyParser.RETURNS), name);
        if(ret != null) {
            return ret;
        }

        DafnyTree var = getVariableDeclInList(function.getFirstChildWithType(DafnyParser.VAR), name);
        return var;
    }

    private DafnyTree getVariableDeclInList(DafnyTree decls, String name) {
        if(decls != null) {
            for (DafnyTree decl : decls.getChildren()) {
                if(decl.getChild(0).getText().equals(name)) {
                    return decl;
                }
            }
        }
        return null;
    }
}
