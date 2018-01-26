package edu.kit.iti.algover.rules.impl;

import edu.kit.iti.algover.ProgramDatabase;
import edu.kit.iti.algover.dafnystructures.*;
import edu.kit.iti.algover.data.BuiltinSymbols;
import edu.kit.iti.algover.data.MapSymbolTable;
import edu.kit.iti.algover.data.SymbolTable;
import edu.kit.iti.algover.parser.*;
import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.rules.*;
import edu.kit.iti.algover.script.interpreter.TermMatcher;
import edu.kit.iti.algover.term.*;
import edu.kit.iti.algover.term.builder.TermBuildException;
import edu.kit.iti.algover.term.builder.TermBuilder;
import edu.kit.iti.algover.term.builder.TreeTermTranslator;
import edu.kit.iti.algover.term.parser.TermParser;
import edu.kit.iti.algover.util.RuleUtil;

import java.io.File;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;

/**
 * Created by jklamroth on 1/25/18.
 */
public class DafnyRule extends AbstractProofRule {
    private String name;
    private String fileName;
    private SymbolTable symbolTable;
    private DafnyTree tree;
    private Term searchTerm;
    private Term replaceTerm;

    public DafnyRule(String file) {
        super(new HashMap<>(), new HashMap<>());
        fileName = file;
        DafnyFile dfi = null;
        try {
            tree = DafnyFileParser.parse(new File(fileName));
            DafnyFileBuilder dfb = new DafnyFileBuilder();
            dfb.setInLibrary(false);
            dfb.setFilename(fileName);
            dfb.parseRepresentation(tree);
            dfi = dfb.build();
        } catch (IOException e) {
            System.out.println("DafnyRule with file name " + fileName + " could not be loaded.");
        } catch (DafnyParserException e) {
            System.out.println("Error parsing rule " + fileName + ".");
        } catch (DafnyException e) {
            System.out.println("Error building Dafny class.");
        }

        Collection<DafnyMethod> methods = dfi.getMethods();
        if(methods.size() != 1) {
            System.out.println("DafnyRuleFiles may only contain EXACTLY one method but found " + methods.size() + ".");
        }
        DafnyMethod method = (DafnyMethod)methods.toArray()[0];
        name = method.getName();

        List<DafnyTree> ensuresClauses = method.getEnsuresClauses();
        if(ensuresClauses.size() != 1) {
            System.out.println("DafnyRules may only contain EXACTLY one ensures but found " + ensuresClauses.size() + ".");
        }
        DafnyTree ensuresClause = ensuresClauses.get(0);

        List<DafnyTree> equalsClauses = ensuresClause.getChildrenWithType(DafnyParser.EQ);
        DafnyTree equalsClause = equalsClauses.get(0);

        symbolTable = makeSymbolTable();
        TreeTermTranslator ttt = new TreeTermTranslator(symbolTable);
        try {
            searchTerm = ttt.build(equalsClause.getChild(0));
            replaceTerm = ttt.build(equalsClause.getChild(1));
        } catch (TermBuildException e) {
            System.out.println("Error parsing equalsClause");
        }
    }

    private Term replaceVarsWithSchemaVars(Term t) {
        if(t instanceof VariableTerm) {
            VariableTerm vt = (VariableTerm)t;
            SchemaVarTerm svt = new SchemaVarTerm(vt.getName(), vt.getSort());
            return svt;
        }
        for(Term term : t.getSubterms()) {
            TermBuilder tb = new TermBuilder(symbolTable);

        }
        return null;
    }

    /**
     *
     * @return Symboltable containing all variable declarations and builtin function symbols
     * Author: Mattias Ulbrich
     */
    private SymbolTable makeSymbolTable() {

        Collection<FunctionSymbol> map = new ArrayList<>();

        for (DafnyTree decl : ProgramDatabase.getAllVariableDeclarations(tree)) {
            String name = decl.getChild(0).toString();
            Sort sort = treeToType(decl.getChild(1));
            map.add(new FunctionSymbol(name, sort));
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

    @Override
    public String getName() {
        return name;
    }

    @Override
    public ProofRuleApplication considerApplication(ProofNode target, Sequent selection, TermSelector selector) throws RuleException {
        return null;
    }

    @Override
    public ProofRuleApplication makeApplication(ProofNode target, Parameters parameters) throws RuleException {
        return null;
    }
}
