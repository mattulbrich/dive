/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 *
 */

package edu.kit.iti.algover.smttrans.translate;

import edu.kit.iti.algover.data.BuiltinSymbols;
import edu.kit.iti.algover.data.SymbolTable;
import edu.kit.iti.algover.parser.DafnyException;
import edu.kit.iti.algover.parser.DafnyParserException;
import edu.kit.iti.algover.parser.DafnyTree;
import edu.kit.iti.algover.project.Project;
import edu.kit.iti.algover.proof.MockPVCBuilder;
import edu.kit.iti.algover.proof.PVC;
import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.rules.ProofRule;
import edu.kit.iti.algover.rules.ProofRuleApplication;
import edu.kit.iti.algover.rules.RuleException;
import edu.kit.iti.algover.rules.TermSelector;
import edu.kit.iti.algover.rules.impl.Z3Rule;
import edu.kit.iti.algover.term.FunctionSymbol;
import edu.kit.iti.algover.term.Sequent;
import edu.kit.iti.algover.term.Sort;
import edu.kit.iti.algover.term.builder.TermBuildException;
import edu.kit.iti.algover.term.parser.TermParser;
import edu.kit.iti.algover.util.ProofMockUtil;
import edu.kit.iti.algover.util.TestUtil;
import edu.kit.iti.algover.util.TreeUtil;

import org.antlr.runtime.RecognitionException;
import org.junit.Before;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameter;
import org.junit.runners.Parameterized.Parameters;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotEquals;

import java.io.BufferedReader;
import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;
import java.util.stream.Stream;

@RunWith(Parameterized.class)
public class MultisetUnitTest {

    private static final String cdir = "modules/core/test-res/edu/kit/iti/algover/smttrans/translate/multiset/completeness".replace('/',
            File.separatorChar);
    private static final String sdir = "modules/core/test-res/edu/kit/iti/algover/smttrans/translate/multiset/soundness".replace('/',
            File.separatorChar);

    @Parameter
    public String name;

    private List<SymbolTable> csymbols = new ArrayList<>();

    private List<Sequent> csequents = new ArrayList<>();
    private List<SymbolTable> ssymbols = new ArrayList<>();

    private List<Sequent> ssequents = new ArrayList<>();

    @Parameters(name = "{0}")
    public static Object[] data() {
        return new Object[] { "multiset" };
    }

    @Before
    public void readAndParseS() throws IOException, DafnyParserException, DafnyException {

        List<Path> paths = Files.walk(Paths.get(sdir)).filter(Files::isRegularFile).collect(Collectors.toList());
        for (Path p : paths) {
            System.out.println(p);
            InputStream stream = Files.newInputStream(p);
            SymbolTable st = new BuiltinSymbols();

            // InputStream stream = getClass().getResourceAsStream(name+"/"+name +
            // ".smt-test");

            BufferedReader r = new BufferedReader(new InputStreamReader(stream));

            String line;
            while ((line = r.readLine()) != null) {
                line = line.trim();
                if (line.startsWith("#") || line.isEmpty()) {
                    continue;
                }

                if (line.equals("---")) {
                    break;
                }

                String[] parts = line.split(" *: *", 2);

                Sort s = TreeUtil.parseSort(parts[1]);
                st.addFunctionSymbol(new FunctionSymbol(parts[0], s));
            }

            StringBuilder sb = new StringBuilder();
            while ((line = r.readLine()) != null) {
                sb.append(line).append("\n");
            }

            this.ssequents.add(TermParser.parseSequent(st, sb.toString()));
            this.ssymbols.add(st);

        }
    }

    
    @Before
    public void readAndParseC() throws IOException, DafnyParserException, DafnyException {

        List<Path> paths = Files.walk(Paths.get(cdir)).filter(Files::isRegularFile).collect(Collectors.toList());
        for (Path p : paths) {
           System.out.println(p);
            InputStream stream = Files.newInputStream(p);
            SymbolTable st = new BuiltinSymbols();

            // InputStream stream = getClass().getResourceAsStream(name+"/"+name +
            // ".smt-test");

            BufferedReader r = new BufferedReader(new InputStreamReader(stream));

            String line;
            while ((line = r.readLine()) != null) {
                line = line.trim();
                if (line.startsWith("#") || line.isEmpty()) {
                    continue;
                }

                if (line.equals("---")) {
                    break;
                }

                String[] parts = line.split(" *: *", 2);

                Sort s = TreeUtil.parseSort(parts[1]);
                st.addFunctionSymbol(new FunctionSymbol(parts[0], s));
            }

            StringBuilder sb = new StringBuilder();
            while ((line = r.readLine()) != null) {
                sb.append(line).append("\n");
            }

            this.csequents.add(TermParser.parseSequent(st, sb.toString()));
            this.csymbols.add(st);

        }
    }

    @Test
    public void verifyZ3C() throws DafnyParserException, DafnyException, RecognitionException, IOException,
            TermBuildException, RuleException {
        for (int i = 0; i < csequents.size(); i++) {

            SymbolTable st = csymbols.get(i);
            Sequent s = csequents.get(i);

            MockPVCBuilder builder = new MockPVCBuilder();
            builder.setSymbolTable(st);
            Project mock = TestUtil.mockProject("method m() ensures true {}"); // not needed
            builder.setSequent(s);
            builder.setDeclaration(mock.getMethod("m")); // not needed
            Map<TermSelector, DafnyTree> mockMap = mock.getPVCByName("m/Post").getReferenceMap(); // not needed
            builder.setReferenceMap(mockMap); // not needed
            PVC pvc = builder.build();
            ProofNode pn = ProofMockUtil.mockProofNode(null, s.getAntecedent(), s.getSuccedent(), pvc);
            ProofRule pr = new Z3Rule();
            ProofRuleApplication pra = pr.makeApplication(pn, new edu.kit.iti.algover.rules.Parameters());
//            if (!pra.getApplicability().equals(ProofRuleApplication.Applicability.APPLICABLE)) {
//                System.err.println(debug.get(i));
//            }
            assertEquals(pra.getApplicability(), ProofRuleApplication.Applicability.APPLICABLE);
        }
    }
    @Test
    public void verifyZ3S() throws DafnyParserException, DafnyException, RecognitionException, IOException,
            TermBuildException, RuleException {
        for (int i = 0; i < ssequents.size(); i++) {

            SymbolTable st = ssymbols.get(i);
            Sequent s = ssequents.get(i);

            MockPVCBuilder builder = new MockPVCBuilder();
            builder.setSymbolTable(st);
            Project mock = TestUtil.mockProject("method m() ensures true {}"); // not needed
            builder.setSequent(s);
            builder.setDeclaration(mock.getMethod("m")); // not needed
            Map<TermSelector, DafnyTree> mockMap = mock.getPVCByName("m/Post").getReferenceMap(); // not needed
            builder.setReferenceMap(mockMap); // not needed
            PVC pvc = builder.build();
            ProofNode pn = ProofMockUtil.mockProofNode(null, s.getAntecedent(), s.getSuccedent(), pvc);
            ProofRule pr = new Z3Rule();
            ProofRuleApplication pra = pr.makeApplication(pn, new edu.kit.iti.algover.rules.Parameters());
//            if (!pra.getApplicability().equals(ProofRuleApplication.Applicability.APPLICABLE)) {
//                System.err.println(debug.get(i));
//            }
            assertNotEquals(pra.getApplicability(), ProofRuleApplication.Applicability.APPLICABLE);
        }
    }
    @Test
    public void verifyCVC() {

    }

}