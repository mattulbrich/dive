package edu.kit.iti.algover;

import edu.kit.iti.algover.parser.PseudoParser;
import edu.kit.iti.algover.parser.PseudoTree;


/**
 * The Class ProgramDatabase serves as database for all information on the
 * program: Defined functions, contracts, declared variables.
 *
 * At the moment, everything is parsed from the AST on demand.
 */
public class ProgramDatabase {

    private final PseudoTree program;

    public ProgramDatabase(PseudoTree program) {
        this.program = program;
    }

    public PseudoTree getFunction(String name) {
        for (PseudoTree f : program.getChildrenWithType(PseudoParser.METHOD)) {
            if(f.getChild(0).getText().equals(name)) {
                return f;
            }
        }
        return null;
    }

    public PseudoTree getVariableDeclaration(PseudoTree function, String name) {
        PseudoTree arg = getVariableDeclInList(function.getFirstChildWithType(PseudoParser.ARGS), name);
        if(arg != null) {
            return arg;
        }

        PseudoTree ret = getVariableDeclInList(function.getFirstChildWithType(PseudoParser.RETURNS), name);
        if(ret != null) {
            return ret;
        }

        PseudoTree var = getVariableDeclInList(function.getFirstChildWithType(PseudoParser.VAR), name);
        return var;
    }

    private PseudoTree getVariableDeclInList(PseudoTree decls, String name) {
        if(decls != null) {
            for (PseudoTree decl : decls.getChildren()) {
                if(decl.getChild(0).getText().equals(name)) {
                    return decl;
                }
            }
        }
        return null;
    }
}
