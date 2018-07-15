package edu.kit.iti.algover.rules;

import edu.kit.iti.algover.ProgramDatabase;
import edu.kit.iti.algover.dafnystructures.DafnyFile;
import edu.kit.iti.algover.dafnystructures.DafnyFileBuilder;
import edu.kit.iti.algover.dafnystructures.DafnyMethod;
import edu.kit.iti.algover.data.BuiltinSymbols;
import edu.kit.iti.algover.data.MapSymbolTable;
import edu.kit.iti.algover.data.SymbolTable;
import edu.kit.iti.algover.parser.*;
import edu.kit.iti.algover.project.Project;
import edu.kit.iti.algover.rules.impl.DafnyRule;
import edu.kit.iti.algover.script.ScriptLanguageLexer;
import edu.kit.iti.algover.term.*;
import edu.kit.iti.algover.term.builder.ReplacementVisitor;
import edu.kit.iti.algover.term.builder.TermBuildException;
import edu.kit.iti.algover.term.builder.TreeTermTranslator;
import edu.kit.iti.algover.util.Pair;

import java.io.File;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.List;
import java.util.stream.Collector;
import java.util.stream.Collectors;

/**
 * Created by jklamroth on 2/1/18.
 * Added to by m. ulbrich.
 */
public class DafnyRuleUtil {
    private static List<String> programVars;


    /**
     * Generates all a DafnyRule for each method of the given project which is a lemma.
     *
     * @param project the project for which the rules are created
     * @return the created rules
     * @throws DafnyRuleException if rule generation fails (see generateRule) or if name of lemma doesn't me requirements
     */
    public static List<DafnyRule> generateDafnyRules(Project project) throws DafnyException {

        Collection<DafnyMethod> methods = project.getMethods();

        List<DafnyRule> result = new ArrayList<>();
        List<String> lemmaRuleNames = new ArrayList<>();

        for (DafnyMethod method : methods) {
            if (method.isLemma()) {
                List<String> builtinRuleNames = project.getBuiltinProofRules().stream().
                        map(ProofRule::getName).
                        collect(Collectors.toList());
                String[] scriptTokens = ScriptLanguageLexer.tokenNames;
                if(lemmaRuleNames.contains(method.getName())) {
                    throw new DafnyException("Duplicated lemma name: " + method.getName(), method.getRepresentation());
                } else if(builtinRuleNames.contains(method.getName())) {
                    //TODO: warning "lemma is going to be hidden due to name conflict with builtin rule"
                } else if(Arrays.asList(scriptTokens).contains(method.getName())) {
                    throw new DafnyException("Script keyword " + method.getName() + " not allowed as name for lemma.", method.getRepresentation());
                }

                try {
                    result.add(generateRule(method));
                } catch (DafnyRuleException e) {
                    throw new DafnyException(method.getRepresentation(), e);
                }

                lemmaRuleNames.add(method.getName());
            }
        }
        return result;
    }

    /**
     * Creates a DafnyRule for a given file.
     *
     * @param fileName path to the file
     * @return the created DafnyRule
     * @throws DafnyRuleException if rule generation fails (see generateRule), if file not found, if parsing cant be done
     */
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
            throw new DafnyRuleException("DafnyRule with file name " + fileName + " could not be loaded.", e);
        } catch (DafnyParserException e) {
            throw new DafnyRuleException("Error parsing rule " + fileName + ".", e);
        } catch (DafnyException e) {
            throw new DafnyRuleException("Error parsing dafny tree for file " + fileName + ".", e);
        }

        Collection<DafnyMethod> methods = dfi.getMethods();
        if(methods.size() != 1) {
            throw new DafnyRuleException("DafnyRuleFiles may only contain EXACTLY one method but found " + methods.size() + ".");
        }
        DafnyMethod method = (DafnyMethod)methods.toArray()[0];
        return generateRule(method);
    }


    /**
     * Generates a DafnyRule from a given DafnyMethod.
     * The method has contain exactly 1 ensures clause which states the substitution the rule is applying.
     * This substitutions may be aquivalences (such applicable on antecedent and succedent) or approximations (as such
     * applicable only on the antecedent or negated on the succedent).
     * An arbitrary number of sideconditions may be stated in requires-clauses. If requires-clause will lead to an
     * additional branch when applying the DafnyRule (except the condition is met trivially).
     *
     * @param method the DafnyMethod
     * @return the generated rule
     * @throws DafnyRuleException if DafnyMethod doesn´t meet requirements for DafnyRule-creation which are:
     *                              - exactly 1 ensures clause
     *                              - ensures clause is either a implication or a aquivalence
     */
    private static DafnyRule generateRule(DafnyMethod method) throws DafnyRuleException {
        String name;
        SymbolTable symbolTable;
        DafnyRule.RulePolarity polarity = DafnyRule.RulePolarity.BOTH;

        // REVIEW How do we deal with name clashes? What if a lemma is called "cut" or "case"?
        // One idea: prefix the name with "lemma_" or "l_". Alternatives?
        name = method.getName();



        List<DafnyTree> ensuresClauses = method.getEnsuresClauses();
        if(ensuresClauses.size() != 1) {
            throw new DafnyRuleException("DafnyRules may only contain EXACTLY one ensures but found " + ensuresClauses.size() + ".");
        }
        DafnyTree ensuresClause = ensuresClauses.get(0);

        List<DafnyTree> requiresClauses = method.getRequiresClauses();


        DafnyTree equalsClause = null;
        DafnyTree implClause = null;
        if(ensuresClause.getChildCount() != 1) {
            throw new DafnyRuleException("The ensures clause has to contain exactly 1 child of either typ EQ or IMPLIES");
        }
        if(ensuresClause.getChild(0).getType() == DafnyParser.EQ) {
            equalsClause = ensuresClause.getChild(0);
        } else if (ensuresClause.getChild(0).getType() == DafnyParser.IMPLIES) {
            implClause = ensuresClause.getChild(0);
        } else {
            throw  new DafnyRuleException("DafnyRules have to contain an equality or implication.");
        }

        symbolTable = makeSymbolTable(method.getRepresentation());
        TreeTermTranslator ttt = new TreeTermTranslator(symbolTable);
        Term st = null;
        Term rt = null;
        List<Pair<Term,String>> rts = new ArrayList<>();

        try {
            if(equalsClause != null) {
                st = ttt.build(equalsClause.getChild(0));
                rt = ttt.build(equalsClause.getChild(1));
                polarity = DafnyRule.RulePolarity.BOTH;
            } else if(implClause != null) {
                st = ttt.build(implClause.getChild(0));
                rt = ttt.build(implClause.getChild(1));
                polarity = DafnyRule.RulePolarity.ANTECEDENT;
            } else {
                throw new DafnyRuleException("No equals or implies clause found.");
            }
            st = st.accept(new ReplaceProgramVariableVisitor(), programVars);
            rt = rt.accept(new ReplaceProgramVariableVisitor(), programVars);
            for(DafnyTree dt : requiresClauses) {
                if(dt.getChildCount() == 1) {
                    Term t = ttt.build(dt.getChild(0));
                    String label = "";
                    rts.add(new Pair<Term, String>(t.accept(new ReplaceProgramVariableVisitor(), programVars), label));
                } else if(dt.getChildCount() == 2) {
                    Term t = ttt.build(dt.getChild(1));
                    String label = dt.getChild(1).getChild(0).toString();
                    rts.add(new Pair<Term, String>(t.accept(new ReplaceProgramVariableVisitor(), programVars), label));
                }

            }
        } catch (TermBuildException e) {
            throw new DafnyRuleException("Error parsing equalsClause", e);
        }
        return new DafnyRule(method, name, st, rt, rts, polarity);
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
            Sort sort = treeToType(decl.getFirstChildWithType(DafnyParser.TYPE).getChild(0));
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


