package edu.kit.iti.algover.rules.impl;

import edu.kit.iti.algover.ProgramDatabase;
import edu.kit.iti.algover.dafnystructures.*;
import edu.kit.iti.algover.data.BuiltinSymbols;
import edu.kit.iti.algover.data.MapSymbolTable;
import edu.kit.iti.algover.data.SymbolTable;
import edu.kit.iti.algover.parser.*;
import edu.kit.iti.algover.proof.ProofFormula;
import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.rules.*;
import edu.kit.iti.algover.term.builder.ReplacementVisitor;
//import edu.kit.iti.algover.term.match.Matching;
//import edu.kit.iti.algover.term.match.TermMatcher;
import edu.kit.iti.algover.term.*;
import edu.kit.iti.algover.term.builder.TermBuildException;
import edu.kit.iti.algover.term.builder.TermBuilder;
import edu.kit.iti.algover.term.builder.TreeTermTranslator;
import edu.kit.iti.algover.util.ImmutableList;
import edu.kit.iti.algover.util.RuleUtil;


import java.io.File;
import java.io.IOException;
import java.util.*;

/**
 * Created by jklamroth on 1/25/18.
 */
public class DafnyRule extends AbstractProofRule {
    private String name;
    private String fileName;
    private SymbolTable symbolTable;
    private List<String> schemaVars;
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
            System.out.println(searchTerm);
            searchTerm = searchTerm.accept(new ReplaceProgrammVariableVisitor(), schemaVars);
            System.out.println(searchTerm);
            replaceTerm = ttt.build(equalsClause.getChild(1));
        } catch (TermBuildException e) {
            System.out.println("Error parsing equalsClause");
        }
    }

    /**
     *
     * @return Symboltable containing all variable declarations and builtin function symbols
     * Author: Mattias Ulbrich
     */
    private SymbolTable makeSymbolTable() {

        Collection<FunctionSymbol> map = new ArrayList<>();
        schemaVars = new ArrayList<>();

        for (DafnyTree decl : ProgramDatabase.getAllVariableDeclarations(tree)) {
            String name = decl.getChild(0).toString();
            Sort sort = treeToType(decl.getChild(1));
            map.add(new FunctionSymbol(name, sort));
            schemaVars.add(name);
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
        /*Term selected = selector.selectTopterm(target.getSequent()).getTerm();
        TermMatcher tm = new TermMatcher();
        ImmutableList<Matching> matchings = tm.match(searchTerm, selected);
        if(matchings.size() == 0) {
            return ProofRuleApplicationBuilder.notApplicable(this);
        }
        ProofRuleApplicationBuilder proofRuleApplicationBuilder;
        try {
            replaceTerm = matchings.get(0).instantiate(replaceTerm);
            proofRuleApplicationBuilder = new ProofRuleApplicationBuilder(this);
            proofRuleApplicationBuilder.setApplicability(ProofRuleApplication.Applicability.APPLICABLE);
            proofRuleApplicationBuilder.setTranscript(getTranscript());
            proofRuleApplicationBuilder.newBranch().addReplacement(selector, replaceTerm);
        } catch (TermBuildException e) {
            throw new RuleException();
        }

        return proofRuleApplicationBuilder.build();*/
        return null;
    }

    @Override
    public ProofRuleApplication makeApplication(ProofNode target, Parameters parameters) throws RuleException {
        /*Term on = parameters.getValue("on").cast(Term.class).getValue();
        TermMatcher tm = new TermMatcher();
        ImmutableList<Matching> matchings = tm.match(searchTerm, on);
        if(matchings.size() == 0) {
            throw new RuleException();
        }

        ProofRuleApplicationBuilder proofRuleApplicationBuilder;
        try {
            replaceTerm = matchings.get(0).instantiate(replaceTerm);
            proofRuleApplicationBuilder = new ProofRuleApplicationBuilder(this);
            if(Optional.empty().equals(RuleUtil.matchTopLevelInAntedecent(on::equals, target.getSequent()))) {
                proofRuleApplicationBuilder.newBranch().addDeletionsSuccedent(new ProofFormula(on)).
                        addAdditionsSuccedent(new ProofFormula(replaceTerm));
            } else {
                proofRuleApplicationBuilder.newBranch().addDeletionsAntecedent(Collections.singletonList(new ProofFormula(on))).
                        addAdditionAntecedent(new ProofFormula(replaceTerm));
            }
        } catch (TermBuildException e) {
            throw new RuleException();
        }

        return proofRuleApplicationBuilder.build();*/
        return null;
    }

    private String getTranscript() {
        String res = name;
        return name;
    }
}

class ReplaceProgrammVariableVisitor extends ReplacementVisitor<List<String>> {

    @Override
    public Term visit(ApplTerm applTerm, List<String> programmVariables) throws TermBuildException {
        if(programmVariables.contains(applTerm.getFunctionSymbol().getName())) {
            return new SchemaVarTerm("?" + applTerm.getFunctionSymbol().getName(), applTerm.getSort());
        } else {
            return super.visit(applTerm, programmVariables);
        }
    }
}