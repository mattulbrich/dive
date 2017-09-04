package edu.kit.iti.algover.rules;

import edu.kit.iti.algover.data.BuiltinSymbols;
import edu.kit.iti.algover.data.MapSymbolTable;
import edu.kit.iti.algover.data.SymbolTable;
import edu.kit.iti.algover.parser.DafnyTree;
import edu.kit.iti.algover.proof.ProofFormula;
import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.rules.impl.TrivialAndRight;
import edu.kit.iti.algover.term.FunctionSymbol;
import edu.kit.iti.algover.term.Sequent;
import edu.kit.iti.algover.term.Sort;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.term.builder.TermBuildException;
import edu.kit.iti.algover.term.builder.TermBuilder;
import edu.kit.iti.algover.term.builder.TreeTermTranslator;
import edu.kit.iti.algover.term.builder.TreeTermTranslatorTest;
import org.antlr.runtime.RecognitionException;
import org.junit.Before;
import org.junit.Test;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

public class TestRuleApplicator {


    ProofRuleApplication prApp;
    SymbolTable symbTable;
    Sequent testSequent;

    Term term1;
    Term term2;
    Term term3;
    Term term4;

    @Before
    public void setup() throws RecognitionException, TermBuildException {
        setupTable();


        TermBuilder tb = new TermBuilder(symbTable);

        TreeTermTranslator ttt = new TreeTermTranslator(symbTable);

        DafnyTree t1 = TreeTermTranslatorTest.parse("b1 || b2 ==> b3");
        DafnyTree t2 = TreeTermTranslatorTest.parse("c == c2");
        DafnyTree t3 = TreeTermTranslatorTest.parse(" b1 && b2");
        DafnyTree t4 = TreeTermTranslatorTest.parse("b1 && b3");

        term1 = ttt.build(t1);
        term2 = ttt.build(t2);
        term3 = ttt.build(t3);
        term4 = ttt.build(t4);

        List<ProofFormula> antec = new ArrayList<>();
        List<ProofFormula> succ = new ArrayList<>();
        antec.add(new ProofFormula(0, term1));
        antec.add(new ProofFormula(0, term2));
        succ.add(new ProofFormula(0, term3));
        succ.add(new ProofFormula(0, term4));
        testSequent = new Sequent(antec, succ);
        //prApp = new ProofRuleApplication()
    }

    @Before
    public void setupTable() {
        Collection<FunctionSymbol> map = new ArrayList<>();
        map.add(new FunctionSymbol("i1", Sort.INT));
        map.add(new FunctionSymbol("i2", Sort.INT));
        map.add(new FunctionSymbol("i3", Sort.INT));
        map.add(new FunctionSymbol("b1", Sort.BOOL));
        map.add(new FunctionSymbol("b2", Sort.BOOL));
        map.add(new FunctionSymbol("b3", Sort.BOOL));
        map.add(new FunctionSymbol("a", Sort.get("array1")));
        map.add(new FunctionSymbol("a2", Sort.get("array2")));
        map.add(new FunctionSymbol("f", Sort.INT, Sort.INT));
        map.add(new FunctionSymbol("c", Sort.getClassSort("C")));
        map.add(new FunctionSymbol("c2", Sort.getClassSort("C")));
        symbTable = new MapSymbolTable(new BuiltinSymbols(), map);
    }

    @Test
    public void test() throws RuleException {
        System.out.println(testSequent);

        ProofRule pr = new TrivialAndRight();
        ProofNode pn = new ProofNode(null, null, null, testSequent, null);

        TermSelector ts = new TermSelector(TermSelector.SequentPolarity.SUCCEDENT, 1);
        Parameters params = new Parameters();
        params.putValue("on", new Parameters.TypedValue<>(Term.class, term3));

        //System.out.println(pr.makeApplication(pn, params));
        //RuleApplicator.applyRule(prApp, new ProofNode(null, null, null, testSequent, null));
        //RuleApplicator.changeSemisequent()

    }

    @Test
    public void testAddAndDelete() throws TermBuildException {
        System.out.println(testSequent.getAntecedent());
        ProofFormula f1 = new ProofFormula(0, term1);
        ProofFormula f2 = new ProofFormula(0, term2);
        ProofFormula f3 = new ProofFormula(0, term3);
        ProofFormula f4 = new ProofFormula(0, term4);
        List<ProofFormula> add = new ArrayList<>();
        add.add(f4);
        add.add(f3);

        List<ProofFormula> del = new ArrayList<>();
        del.add(f2);

        List<ProofFormula> testSemi = testSequent.getAntecedent();

        System.out.println(RuleApplicator.changeSemisequent(add, del, new ArrayList<>(), testSemi));
    }
}
