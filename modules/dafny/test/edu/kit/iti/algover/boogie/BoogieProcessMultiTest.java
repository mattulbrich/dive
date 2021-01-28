package edu.kit.iti.algover.boogie;

import edu.kit.iti.algover.data.BuiltinSymbols;
import edu.kit.iti.algover.project.Project;
import edu.kit.iti.algover.proof.MockPVCBuilder;
import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.term.FunctionSymbol;
import edu.kit.iti.algover.term.Sequent;
import edu.kit.iti.algover.term.Sort;
import edu.kit.iti.algover.term.parser.TermParser;
import edu.kit.iti.algover.util.LineProperties;
import edu.kit.iti.algover.util.TestUtil;
import edu.kit.iti.algover.util.Util;
import org.junit.Before;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameter;
import org.junit.runners.Parameterized.Parameters;

import java.net.URL;
import java.util.ArrayList;
import java.util.List;

import static org.junit.Assert.*;

// The Boogie translation of individual cases is best tested using the
// BoogieProcessTest. This here is for multi-sequent translations.
// But heavily inspired by that class.
@RunWith(Parameterized.class)
public class BoogieProcessMultiTest {

    private Project project;
    private Sequent sequent1;
    private List<Sequent> sequents;
    private List<ProofNode> proofNodes;
    private String expectedTranslation;

    @Parameters(name = "{1}")
    public static List<Object[]> parameters() throws Exception {
        String packagePath = BoogieProcessMultiTest.class.getPackageName().replace('.', '/');
        String path = packagePath + "/multi";
        List<URL> list = TestUtil.getResourcesIn(path, "boogie", false);
        return Util.map(list, l->new Object[] { l, l.getFile().substring(l.getFile().lastIndexOf('/')+1) });
    }

    @Parameter
    public URL url;

    @Parameter(1)
    public String name;

    @Before
    public void setup() throws Exception {

        LineProperties props = new LineProperties();
        props.read(url.openStream());

        this.project = TestUtil.mockProject(
                props.getOrDefault("project",
                        "method m() {}"));

        this.sequents = new ArrayList<>();
        this.proofNodes = new ArrayList<>();

        int c = 1;
        while(true) {
            if(!props.containsKey("sequent" + c)) {
                break;
            }
            BuiltinSymbols table = new BuiltinSymbols();
            project.getAllDeclaredSymbols().forEach(table::addFunctionSymbol);
            for (String line : props.getLines("decls"+c)) {
                String[] parts = line.split(" *(\\*|:|->) *");
                String name = parts[0];
                Sort resultSort = Sort.parseSort(parts[parts.length - 1]);
                Sort args[] = new Sort[parts.length - 2];
                for (int i = 0; i < args.length; i++) {
                    args[i] = Sort.parseSort(parts[i + 1]);
                }
                FunctionSymbol fs = new FunctionSymbol(name, resultSort, args);
                table.addFunctionSymbol(fs);
            }
            Sequent sequent = TermParser.parseSequent(table, props.get("sequent" + c));
            sequents.add(sequent);
            MockPVCBuilder b = new MockPVCBuilder();
            b.setSequent(sequent);
            ProofNode proofNode;
            proofNode = ProofNode.createRoot(b.build());
            proofNodes.add(proofNode);

            c++;
        }

        this.expectedTranslation = props.get("translation");
    }

    @Test
    public void testBoogieTranslation() throws Exception {

        BoogieProcess bt = new BoogieProcess(project, project.getBaseSymbolTable(), proofNodes);
        String actual = bt.getBoogieCode();

        assertEquals(expectedTranslation.trim(), actual.trim());
    }
}