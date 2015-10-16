package edu.kit.iti.algover;

import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import edu.kit.iti.algover.parser.DafnyParser;
import edu.kit.iti.algover.parser.DafnyTree;
import edu.kit.iti.algover.term.FunctionSymbol;


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

    public DafnyTree getMethod(String name) {
        for (DafnyTree f : program.getChildrenWithType(DafnyParser.METHOD)) {
            if(f.getChild(0).getText().equals(name)) {
                return f;
            }
        }
        return null;
    }

    /**
     * Fuer PVC SymbTable
     * @param method
     * @return
     * TODO Mattias Ulbrich
     */
    public static List<DafnyTree> getAllVariableDeclarations(DafnyTree method) {
        List<DafnyTree> allDeclarations = new LinkedList<DafnyTree>();

        return allDeclarations;
    }
    public static DafnyTree getVariableDeclaration(DafnyTree method, String name) {
        DafnyTree arg = getVariableDeclInList(method.getFirstChildWithType(DafnyParser.ARGS), name);
        if(arg != null) {
            return arg;
        }

        DafnyTree ret = getVariableDeclInList(method.getFirstChildWithType(DafnyParser.RETURNS), name);
        if(ret != null) {
            return ret;
        }

        DafnyTree var = getVariableDeclInList(method.getFirstChildWithType(DafnyParser.VAR), name);
        return var;
    }

    private static DafnyTree getVariableDeclInList(DafnyTree decls, String name) {
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
