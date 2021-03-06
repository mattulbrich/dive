/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.rule;

import edu.kit.iti.algover.ApplicationTest;
import edu.kit.iti.algover.MainController;
import edu.kit.iti.algover.ProjectManagerMock;
import edu.kit.iti.algover.browser.entities.PVCEntity;
import edu.kit.iti.algover.project.ProjectManager;
import edu.kit.iti.algover.rules.TermSelector;
import edu.kit.iti.algover.util.FormatException;
import javafx.scene.Parent;
import javafx.scene.layout.StackPane;

public class RuleApplicationTest extends ApplicationTest {
    private static final String PVCID = "gcd/InitInv.1";

    @Override
    protected Parent constructView() throws FormatException {
        ProjectManager manager = ProjectManagerMock.fromExample("gcd");
        MainController controller = new MainController(manager, SYNTAX_HIGHLIGHTING_EXECUTOR);
        controller.onClickPVCEdit(
                new PVCEntity(manager.getProofForPVC(PVCID), manager.getPVCByNameMap().get(PVCID), manager.getProject().getDafnyFiles().get(0)));
        controller.onClickSequentSubterm(new TermSelector("S.0"));
        return new StackPane(controller.getView());
    }
}
