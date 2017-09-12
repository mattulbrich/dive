package edu.kit.iti.algover;

import edu.kit.iti.algover.project.ProjectManager;
import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.proof.ProofNodeSelector;
import edu.kit.iti.algover.references.ProofTermReference;
import edu.kit.iti.algover.references.Reference;
import edu.kit.iti.algover.references.ReferenceGraph;
import edu.kit.iti.algover.rule.RuleApplicationController;
import edu.kit.iti.algover.browser.BrowserController;
import edu.kit.iti.algover.browser.FlatBrowserController;
import edu.kit.iti.algover.browser.entities.PVCEntity;
import edu.kit.iti.algover.browser.entities.PVCGetterVisitor;
import edu.kit.iti.algover.browser.entities.TreeTableEntity;
import edu.kit.iti.algover.dafnystructures.DafnyFile;
import edu.kit.iti.algover.editor.EditorController;
import edu.kit.iti.algover.proof.PVC;
import edu.kit.iti.algover.rules.TermSelector;
import edu.kit.iti.algover.sequent.SequentActionListener;
import edu.kit.iti.algover.sequent.SequentController;
import edu.kit.iti.algover.timeline.TimelineLayout;

import java.util.Set;

/**
 * Created by philipp on 27.06.17.
 */
public class OverviewController implements SequentActionListener {

    private final ProjectManager manager;
    private final BrowserController browserController;
    private final EditorController editorController;
    private final SequentController sequentController;
    private final RuleApplicationController ruleApplicationController;
    private final TimelineLayout view;

    public OverviewController(ProjectManager manager) {
        this.manager = manager;
        this.browserController = new FlatBrowserController(manager.getProject(), this::onClickPVCEdit);
        //this.browserController = new FileBasedBrowserController(manager.getProject(), this::onClickPVCEdit);
        this.editorController = new EditorController();
        this.sequentController = new SequentController(manager, this);
        this.ruleApplicationController = new RuleApplicationController(manager);

        this.view = new TimelineLayout(
                browserController.getView(),
                editorController.getView(),
                sequentController.getView(),
                ruleApplicationController.getView());
        view.setDividerPosition(0.2);

        browserController.setSelectionListener(this::onSelectBrowserItem);
    }

    private void onClickPVCEdit(PVCEntity entity) {
        PVC pvc = entity.getPVC();
        editorController.viewFile(entity.getLocation());
        editorController.viewPVCSelection(pvc);
        sequentController.viewSequentForPVC(entity);
        ruleApplicationController.resetConsideration();
        view.moveFrameRight();
    }

    private void onSelectBrowserItem(TreeTableEntity treeTableEntity) {
        DafnyFile file = treeTableEntity.getLocation();
        if (file != null) {
            editorController.viewFile(file);
            PVC pvc = treeTableEntity.accept(new PVCGetterVisitor());
            if (pvc != null) {
                editorController.viewPVCSelection(pvc);
            } else {
                editorController.resetPVCSelection();
            }
        }
    }

    @Override
    public void cancelProofEditing() {
        view.moveFrameLeft();
    }

    @Override
    public void clickOnSubterm(TermSelector selector) {
        view.moveFrameRight();
        ProofNode node = sequentController.getActiveProofNode();
        if (node != null) {
            ruleApplicationController.considerApplication(node, node.getSequent(), selector);
        }
    }

    @Override
    public void hoverOverSubterm(TermSelector selector) {
        if (selector != null) {
            Reference termRef =
                    new ProofTermReference(new ProofNodeSelector(sequentController.getActiveProofNode()), selector);
            Set<Reference> predecessors = sequentController.getReferenceGraph().allPredecessors(termRef);
            System.out.println(predecessors);
            System.out.println("-----------------------------------");
        }
    }

    public TimelineLayout getView() {
        return view;
    }
}
