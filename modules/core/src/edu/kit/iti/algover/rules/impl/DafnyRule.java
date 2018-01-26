package edu.kit.iti.algover.rules.impl;

import edu.kit.iti.algover.dafnystructures.DafnyClass;
import edu.kit.iti.algover.dafnystructures.DafnyClassBuilder;
import edu.kit.iti.algover.dafnystructures.DafnyFunction;
import edu.kit.iti.algover.parser.*;
import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.rules.*;
import edu.kit.iti.algover.term.Sequent;

import java.io.File;
import java.io.IOException;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;

/**
 * Created by jklamroth on 1/25/18.
 */
public class DafnyRule extends AbstractProofRule {
    private String name;
    private String fileName;
    private DafnyTree tree;

    public DafnyRule(String file) {
        super(new HashMap<>(), new HashMap<>());
        fileName = file;
        DafnyClassBuilder dcb = new DafnyClassBuilder();
        DafnyClass dc = null;
        try {
            tree = DafnyFileParser.parse(new File(fileName));
            dcb.setFilename(fileName);
            dc = dcb.build();
        } catch (IOException e) {
            System.out.println("DafnyRule with file name " + fileName + " could not be loaded.");
        } catch (DafnyParserException e) {
            System.out.println("Error parsing rule " + fileName + ".");
        } catch (DafnyException e) {
            System.out.println("Error building Dafny class.");
        }

        Collection<DafnyFunction> functions = dc.getFunctions();
        name = functions.toArray()[0].toString();
        System.out.println("name = " + name);
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
