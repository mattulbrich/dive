package edu.kit.iti.algover;

import edu.kit.iti.algover.project.ProjectManager;
import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.proof.ProofNodeSelector;
import edu.kit.iti.algover.references.*;
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

import java.util.HashSet;
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
    public void considerApplication(TermSelector selector) {
        view.moveFrameRight();
        ProofNode node = sequentController.getActiveProofNode();
        if (node != null) {
            ruleApplicationController.considerApplication(node, node.getSequent(), selector);
        }
    }

    @Override
    public void requestReferenceHighlighting(TermSelector selector) {
        if (selector != null) {
            Reference termRef =
                    new ProofTermReference(new ProofNodeSelector(sequentController.getActiveProofNode()), selector);
            Set<Reference> predecessors = sequentController.getReferenceGraph().allPredecessors(termRef);
            Set<CodeReference> codeReferences = filterCodeReferences(predecessors);
            codeReferences.forEach(codeReference -> {
                System.out.println(codeReference);
                System.out.println(
                        codeReference.accept(new ReferencePrettyPrinter(sequentController.getActiveProof(), 100)));
            });
            editorController.viewReferences(codeReferences);
        }
    }

    private static Set<CodeReference> filterCodeReferences(Set<Reference> predecessors) {
        Set<CodeReference> codeReferences = new HashSet<>();
        predecessors.forEach(reference -> {
            reference.accept(new ReferenceVisitor<Void>() {
                @Override
                public Void visit(CodeReference codeTarget) {
                    codeReferences.add(codeTarget);
                    return null;
                }

                @Override
                public Void visit(ProofTermReference termTarget) {
                    return null;
                }

                @Override
                public Void visit(UserInputReference userInputTarget) {
                    return null;
                }
            });
        });
        return codeReferences;
    }

    public TimelineLayout getView() {
        return view;
    }
}
