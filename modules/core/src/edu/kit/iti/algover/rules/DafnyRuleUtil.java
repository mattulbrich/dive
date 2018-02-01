package edu.kit.iti.algover.rules;

import edu.kit.iti.algover.ProgramDatabase;
import edu.kit.iti.algover.dafnystructures.DafnyFile;
import edu.kit.iti.algover.dafnystructures.DafnyFileBuilder;
import edu.kit.iti.algover.dafnystructures.DafnyMethod;
import edu.kit.iti.algover.data.BuiltinSymbols;
import edu.kit.iti.algover.data.MapSymbolTable;
import edu.kit.iti.algover.data.SymbolTable;
import edu.kit.iti.algover.parser.*;
import edu.kit.iti.algover.rules.impl.DafnyRule;
import edu.kit.iti.algover.term.*;
import edu.kit.iti.algover.term.builder.ReplacementVisitor;
import edu.kit.iti.algover.term.builder.TermBuildException;
import edu.kit.iti.algover.term.builder.TreeTermTranslator;

import java.io.File;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

/**
 * Created by jklamroth on 2/1/18.
 */
public class DafnyRuleUtil {
    private static List<String> programVars;

    public static DafnyRule generateDafnyRuleFromFile(String fileName)  throws DafnyRuleException {
        String name;
        SymbolTable symbolTable;
        DafnyTree tree = null;
        DafnyFile dfi = null;

        try {
            tree = DafnyFileParser.parse(new File(fileName));
            DafnyFileBuilder dfb = new DafnyFileBuilder();
            dfb.setInLibrary(false);
            dfb.setFilename(fileName);
            dfb.parseRepresentation(tree);
            dfi = dfb.build();
        } catch (IOException e) {
            throw new DafnyRuleException("DafnyRule with file name " + fileName + " could not be loaded.");
        } catch (DafnyParserException e) {
            throw new DafnyRuleException("Error parsing rule " + fileName + ".");
        } catch (DafnyException e) {
            throw new DafnyRuleException("Error parsing dafny tree for file " + fileName + ".");
        }

        Collection<DafnyMethod> methods = dfi.getMethods();
        if(methods.size() != 1) {
            throw new DafnyRuleException("DafnyRuleFiles may only contain EXACTLY one method but found " + methods.size() + ".");
        }
        DafnyMethod method = (DafnyMethod)methods.toArray()[0];
        name = method.getName();

        List<DafnyTree> ensuresClauses = method.getEnsuresClauses();
        if(ensuresClauses.size() != 1) {
            throw new DafnyRuleException("DafnyRules may only contain EXACTLY one ensures but found " + ensuresClauses.size() + ".");
        }
        DafnyTree ensuresClause = ensuresClauses.get(0);

        List<DafnyTree> equalsClauses = ensuresClause.getChildrenWithType(DafnyParser.EQ);
        DafnyTree equalsClause = equalsClauses.get(0);

        symbolTable = makeSymbolTable(tree);
        TreeTermTranslator ttt = new TreeTermTranslator(symbolTable);
        Term st = null;
        Term rt = null;
        try {
            st = ttt.build(equalsClause.getChild(0));
            st = st.accept(new ReplaceProgramVariableVisitor(), programVars);
            rt = ttt.build(equalsClause.getChild(1));
            rt = rt.accept(new ReplaceProgramVariableVisitor(), programVars);
        } catch (TermBuildException e) {
            throw new DafnyRuleException("Error parsing equalsClause");
        }
        return new DafnyRule(name, st, rt);
    }

    /**
     *
     * @return Symboltable containing all variable declarations and builtin function symbols
     * Author: Mattias Ulbrich
     */
    private static SymbolTable makeSymbolTable(DafnyTree tree) {

        Collection<FunctionSymbol> map = new ArrayList<>();
        programVars = new ArrayList<>();

        for (DafnyTree decl : ProgramDatabase.getAllVariableDeclarations(tree)) {
            String name = decl.getChild(0).toString();
            Sort sort = treeToType(decl.getChild(1));
            map.add(new FunctionSymbol(name, sort));
            programVars.add(name);
        }

        MapSymbolTable st = new MapSymbolTable(new BuiltinSymbols(), map);
        return st;
    }

    private static Sort treeToType(DafnyTree tree) {
        String name = tree.toString();
        if("array".equals(name)) {
            name = "array1";
        }
        return Sort.get(name);
    }
}

class ReplaceProgramVariableVisitor extends ReplacementVisitor<List<String>> {
    @Override
    public Term visit(ApplTerm applTerm, List<String> programmVariables) throws TermBuildException {
        if(programmVariables.contains(applTerm.getFunctionSymbol().getName())) {
            return new SchemaVarTerm("?" + applTerm.getFunctionSymbol().getName(), applTerm.getSort());
        } else {
            return super.visit(applTerm, programmVariables);
        }
    }
}
